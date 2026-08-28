package souther.compiler.check;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

import souther.compiler.check.ElementProvenance.CopyableFactKind;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;

import java.util.Map;
import java.util.function.BiConsumer;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What was proved of a body's bindings is said again of the bindings a copy of that body was given.
 *
 * <p>Two things are held here, and they are not the same thing. The law is about facts and a
 * renaming: both ends moved or nothing induced, and the fact already written left where it is. What
 * the models hold is that the law is applied where a body is copied at all, which is what a walk
 * standing inside another walk's closure needs and what no law about a map can say.
 *
 * <p>The law is held by the map and not through a model, because no source reaches its edges. Every
 * fact here is one binding of an expansion said of another the same expansion wrote, so a renaming
 * that moved one end and not the other is not a state a body compiles into. What can be asked of the
 * primitive is the law itself, over bindings made by hand.
 */
class WhatWasProvedOfABodyIsSaidAgainOfEveryCopyOfItTest {

    private static final BindingOwner WRITTEN = new BindingOwner.OfValue("example.claims", "f");
    private static final BindingOwner COPIED = new BindingOwner.OfValue("example.claims", "g");

    private static final BindingId OF = new BindingId(WRITTEN, 0);
    private static final BindingId FROM = new BindingId(WRITTEN, 1);
    private static final BindingId OF_HERE = new BindingId(COPIED, 0);
    private static final BindingId FROM_HERE = new BindingId(COPIED, 1);

    /**
     * Both ends moved: the copy has the same fact of the bindings it was given, and the body it was
     * taken from keeps its own.
     *
     * <p>Asked of every kind, so a fourth added to the table is carried by the same law or fails
     * here. What records it is chosen by a switch over the kinds with no default, so a kind added
     * and not recorded does not reach this test at all.
     */
    @ParameterizedTest
    @EnumSource(CopyableFactKind.class)
    void bothEndsMovedInducesTheFactOfTheCopy(CopyableFactKind kind) {
        assertEquals(Map.of(OF, FROM, OF_HERE, FROM_HERE),
                carried(kind, Map.of(OF, OF_HERE, FROM, FROM_HERE)).of(kind),
                "the copy's bindings have between them what the body's had, and the body it was"
                        + " copied from is a body too, so its own fact stays as it was");
    }

    /**
     * One end moved is not this copy's fact, and half of it renamed would say of one body's binding
     * what was proved about another's.
     *
     * <p>The whole table either way round. What a half-renamed fact does is either put one under a
     * binding the copy made or rewrite the end of the one already there, and only reading all of it
     * says neither happened — asked of the moved binding alone, the second goes unseen.
     */
    @ParameterizedTest
    @EnumSource(CopyableFactKind.class)
    void oneEndMovedInducesNothing(CopyableFactKind kind) {
        assertEquals(Map.of(OF, FROM), carried(kind, Map.of(OF, OF_HERE)).of(kind),
                "the binding a fact is said of moved and the one it is said of did not");
        assertEquals(Map.of(OF, FROM), carried(kind, Map.of(FROM, FROM_HERE)).of(kind),
                "and the other way round: the end this fact is said of is where it was");
    }

    /** A renaming that moves neither end moves nothing. */
    @ParameterizedTest
    @EnumSource(CopyableFactKind.class)
    void aRenamingOfOtherBindingsInducesNothing(CopyableFactKind kind) {
        assertEquals(Map.of(OF, FROM),
                carried(kind, Map.of(new BindingId(WRITTEN, 9), OF_HERE)).of(kind),
                "a copy of some other part of the body says nothing about this fact");
    }

    /**
     * A binding a copy just minted is one nothing has spoken of, so meeting it already answered is
     * two bindings given one name rather than a fact arriving twice.
     *
     * <p>Two ways it can be met and one thing that must not happen. The binding is already spoken
     * for in the table, which is a copy before this one having minted it; or twice within this
     * copy, which is this renaming naming two of the body's bindings alike. Asked of the table
     * alone, the second goes through and one of the two facts is quietly the other.
     */
    @Test
    void aBindingAlreadySpokenForInTheTableIsRefused() {
        ElementProvenance.Builder builder = new ElementProvenance.Builder();
        record(builder, CopyableFactKind.PROJECTS_EACH_ELEMENT_OF, OF, FROM);
        record(builder, CopyableFactKind.PROJECTS_EACH_ELEMENT_OF, OF_HERE, FROM_HERE);

        assertThrows(IllegalStateException.class,
                () -> builder.carriedAcross(Map.of(OF, OF_HERE, FROM, FROM_HERE)),
                "the binding this copy would write under is one the table already answers");
    }

    /** And a renaming naming two of the body's bindings alike is refused for the same reason. */
    @Test
    void twoOfTheBodysBindingsGivenOneNameAreRefused() {
        BindingId alsoOf = new BindingId(WRITTEN, 2);
        BindingId alsoFrom = new BindingId(WRITTEN, 3);
        ElementProvenance.Builder builder = new ElementProvenance.Builder();
        record(builder, CopyableFactKind.PROJECTS_EACH_ELEMENT_OF, OF, FROM);
        record(builder, CopyableFactKind.PROJECTS_EACH_ELEMENT_OF, alsoOf, alsoFrom);

        assertThrows(IllegalStateException.class,
                () -> builder.carriedAcross(Map.of(OF, OF_HERE, FROM, FROM_HERE,
                        alsoOf, OF_HERE, alsoFrom, new BindingId(COPIED, 3))),
                "both facts would be written under the one binding, and one of them would be the"
                        + " other with nothing saying so");
    }

    /** Nothing recorded stays nothing, whatever a copy renames. */
    @Test
    void aBodyWithNothingProvedOfItCarriesNothing() {
        ElementProvenance.Builder builder = new ElementProvenance.Builder();
        builder.carriedAcross(Map.of(OF, OF_HERE, FROM, FROM_HERE));
        assertTrue(builder.built().isEmpty(), "a copy induces facts and does not invent them");
    }

    /**
     * The lifetime, which the law alone does not give: a walk inside another walk's closure is read
     * as the run it is read as in a body.
     *
     * <p>The closure is applied where the operation that hands it its elements was spliced in, so
     * its body — already expanded, the walk inside it already proved of — is copied there, and every
     * binding the reading looks for is one that copy made.
     */
    @Test
    void aWalkInsideAnothersClosureIsRead() {
        ElementBindings elements = elements("insideAClosure");
        assertFalse(elements.projected().isEmpty(),
                "the walk answers a place of its element, and the licence is on that element");
        assertEquals("amount",
                elements.projectionAt(elements.projected().keySet().iterator().next()).toString());
    }

    /**
     * And a second closure between the walk and the body changes nothing.
     *
     * <p>Not a second copy: what the outer closure's body holds by the time it is copied is the
     * inner walk already expanded, so one renaming carries both. What this holds is that a shape an
     * author writes — a walk reached through two closures rather than one — reads like the shape
     * above, and it says nothing about when the carrying happens.
     */
    @Test
    void aWalkReachedThroughTwoClosuresIsRead() {
        ElementBindings elements = elements("twoClosuresDeep");
        assertFalse(elements.projected().isEmpty(),
                "the licence is on the element however many closures stand between the walk and"
                        + " the body");
    }

    private static ElementProvenance carried(CopyableFactKind kind,
                                             Map<BindingId, BindingId> renaming) {
        ElementProvenance.Builder builder = new ElementProvenance.Builder();
        record(builder, kind, OF, FROM);
        builder.carriedAcross(renaming);
        return builder.built();
    }

    /** One fact of the given kind, written down. A switch over the kinds and no default, so a kind
     *  added to the table is a kind this test does not compile without. */
    private static void record(ElementProvenance.Builder builder, CopyableFactKind kind,
                               BindingId of, BindingId from) {
        BiConsumer<BindingId, BindingId> into = switch (kind) {
            case HOLDS_THE_SAME_AS -> builder::holdsTheSameAs;
            case DERIVES_FROM -> builder::derivesFrom;
            case PROJECTS_EACH_ELEMENT_OF -> builder::projectsEachElementOf;
        };
        into.accept(of, from);
    }

    private static final String MODEL = """
            module example.claims

            data Amount = Int
                invariant value >= 0

            data Item = { amount: Amount, free: Bool }

            data Big = { threshold: Int }
            data Small
            data Kind = Big | Small

            data Needed
            data NotNeeded
            data Verdict = Needed | NotNeeded

            let matches (lines: List<Item>, k: Kind): Bool =
                match k with
                    | Big { threshold } ->
                        List.sum(List.map(line -> line.amount.value, lines)) >= threshold
                    | Small -> false

            behavior insideAClosure : (lines: List<Item>, kinds: List<Kind>) -> Verdict
            let insideAClosure (lines, kinds) =
                if List.length(List.filter(k -> matches(lines, k), kinds)) >= 1
                    then Needed else NotNeeded

            behavior twoClosuresDeep : (lines: List<Item>, kinds: List<Kind>, tags: List<Int>)
                    -> Verdict
            let twoClosuresDeep (lines, kinds, tags) =
                if List.length(List.filter(t -> List.any(k -> matches(lines, k), kinds), tags))
                        >= 1 then Needed else NotNeeded
            """;

    private static ElementBindings elements(String behavior) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        Bodies.CheckedBody checked = compilation.db().ask(new Bodies.CheckedBehavior(
                compilation.modules().get(0), behavior)).value();
        return checked.elements();
    }
}
