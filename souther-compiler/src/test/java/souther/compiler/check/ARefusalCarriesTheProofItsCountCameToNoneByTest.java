package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Compilation;
import souther.compiler.types.TypeSymbol;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a group with no value is reported as having been shown by.
 *
 * <p>A refusal was one sentence for as long as nothing carried an answer to "how was this shown", so
 * every way of coming to no value was told the way one of them came to it. What is asserted here is
 * the proof itself and not the sentence: the proof is what travels with the count, and the sentence
 * is chosen from it in one place.
 *
 * <p>The proof read is the one the group is established by — everything outside it granted — and it
 * is taken once the declaration to report at is settled. Which member of a group reaches the others
 * how is that member's own, so a proof taken before the anchor is settled would suggest to one member
 * what is true of another.
 */
class ARefusalCarriesTheProofItsCountCameToNoneByTest {

    private static List<UninhabitableTypes.UninhabitableGroup> reported(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                        .flatMap(List::stream).map(each -> each.diagnostic().code().toString())
                        .filter(each -> !each.equals("E1013")).toList(),
                "the model this reads has to be one somebody could write");
        List<souther.compiler.ast.Hir.Def> defs =
                compilation.module("demo").defs().stream().map(Derived.Def::read).toList();
        return UninhabitableTypes.withNoValueOfTheirOwn(defs,
                TypeCardinality.solve(defs, compilation.symbols("demo")));
    }

    private static Emptiness only(String source) {
        List<UninhabitableTypes.UninhabitableGroup> reported = reported(source);
        assertEquals(1, reported.size(), "one group to say something about");
        return reported.get(0).why();
    }

    private static List<String> named(List<TypeSymbol> these) {
        return these.stream().map(TypeSymbol::name).toList();
    }

    /** Rules that contradict, which is what the one sentence written before never said. */
    @Test
    void rulesThatCannotAllHoldAreCarriedAsThat() {
        assertEquals(new Emptiness.ConflictingRules(), only("""
                module demo

                data Bad = Int
                    invariant no = value >= 2 && value <= 1
                """));
    }

    /** A set too small for its element, carried with the two counts that do not meet. */
    @Test
    void aSetTooSmallForItsElementIsCarriedWithBothCounts() {
        assertEquals(new Emptiness.AtAField(FieldDomains.THE_VALUE,
                        new Emptiness.SetRequiresTooManyDistinctValues(2, 1)), only("""
                module demo

                data One = Int
                    invariant only = value >= 1 && value <= 1

                data Pair = Set<One>
                    invariant two = Set.size(value) >= 2
                """));
    }

    /** And the same at a field, where the position the proof names is the field. */
    @Test
    void thePositionAProofNamesIsWhereTheRulesWereWritten() {
        assertEquals(new Emptiness.AtAField("pair",
                        new Emptiness.SetRequiresTooManyDistinctValues(2, 1)), only("""
                module demo

                data One = Int
                    invariant only = value >= 1 && value <= 1

                data Holder = { pair: Set<One> }
                    invariant two = Set.size(pair) >= 2
                """));
    }

    /**
     * A cycle is shown by the rising having stopped with all of them at nothing.
     *
     * <p>Not by either of them naming the other. That {@code A} has no value because {@code B} has
     * none and {@code B} because {@code A} has is two true statements and no proof, and it is what
     * the reading has to hand while it is still running. What makes it a proof is the least fixed
     * point having been reached, which is the one thing neither declaration says.
     */
    @Test
    void aCycleIsCarriedAsTheRisingHavingStoppedWithNothingShown() {
        Emptiness why = only("""
                module demo

                data A = { b: B }
                data B = { a: A }
                """);
        if (!(why instanceof Emptiness.NoBaseInComponent it)) {
            throw new AssertionError("shown by the rising and not by one of them naming the other: " + why);
        }
        assertEquals(List.of("A", "B"), named(it.members()));
        assertEquals("b", ((Emptiness.AtAField) it.through()).path(),
                "and how the one reported reaches the rest, which is what a suggestion is read off");
    }

    /**
     * A member of a cycle with a lack of its own is separated out and keeps its own proof.
     *
     * <p>Both readings run over the same declarations. What tells them apart is granting: {@code Bad}
     * has none with everything else granted, and {@code A} and {@code B} still have none with
     * {@code Bad} granted.
     */
    @Test
    void aLackOfItsOwnBesideACycleKeepsBothProofs() {
        List<UninhabitableTypes.UninhabitableGroup> reported = reported("""
                module demo

                data Bad = Int
                    invariant no = value >= 2 && value <= 1

                data A = { b: B }
                data B = { a: A, bad: Bad }
                """);
        assertEquals(List.of(List.of("Bad"), List.of("A", "B")),
                reported.stream().map(each -> named(each.members())).toList());
        assertEquals(new Emptiness.ConflictingRules(), reported.get(0).why());
        if (!(reported.get(1).why() instanceof Emptiness.NoBaseInComponent)) {
            throw new AssertionError("the cycle is left with nothing to bottom out: "
                    + reported.get(1).why());
        }
    }

    /**
     * Rules of a declaration's own are nearer than anything a field of it lacks.
     *
     * <p>Both are true of this one at once. Which is carried has to be settled by something other
     * than which the reading reached first, or the same model is refused for a different reason each
     * time a field moves.
     */
    @Test
    void aLackOfItsOwnIsNearerThanOneItReaches() {
        String before = """
                module demo

                data Bad = Int
                    invariant no = value >= 2 && value <= 1

                data Both = { held: Bad, n: Int }
                    invariant no = n >= 2 && n <= 1
                """;
        String after = """
                module demo

                data Bad = Int
                    invariant no = value >= 2 && value <= 1

                data Both = { n: Int, held: Bad }
                    invariant no = n >= 2 && n <= 1
                """;
        assertEquals(new Emptiness.ConflictingRules(), reported(before).get(1).why());
        assertEquals(new Emptiness.ConflictingRules(), reported(after).get(1).why(),
                "and the fields the other way round");
    }
}
