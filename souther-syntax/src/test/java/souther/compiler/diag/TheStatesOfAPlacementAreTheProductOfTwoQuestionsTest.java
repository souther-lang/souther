package souther.compiler.diag;

import org.junit.jupiter.api.Test;

import souther.compiler.source.SourceId;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@link Placement} is the product of two questions, and the questions are independent.
 *
 * <p>Which text a position is in, and whose code it carries. They looked like one question and are
 * not: a text put back together out of what a module published has real positions carrying that
 * module's own code, and no reader holds a file those numbers are of. Being unable to show a text
 * and carrying somebody else's code are different facts.
 *
 * <p>What this holds is that they stay independent. Every pair is reachable, a splice moves exactly
 * one of them, and each of the three projections a reader may ask for is decided by the components
 * it is about — {@code quotedFrom} by the text alone, where the code is written by both.
 *
 * <p>This is not type safety. The compiler already refuses an arm that does not implement what its
 * interface declares. What this holds is the other half — that the states are the ones somebody
 * designed, and have not drifted into being a list. A seventh state either fills a pair already
 * filled, in which case it is one of these six written wrongly, or it answers neither question, in
 * which case whoever proposes it has found a third question and owes an account of it.
 *
 * <p>The states are not named here. Naming them would make this a copy of the declaration, green on
 * the day a seventh was added and left off the copy. What is named is the two questions, and the
 * states are reached the way every caller reaches them.
 */
class TheStatesOfAPlacementAreTheProductOfTwoQuestionsTest {

    private static final SourceProvenance LIB =
            new SourceProvenance.APublishedModule("lib.rule", "lib.rule.atLeast");
    private static final SourceProvenance OTHER =
            new SourceProvenance.APublishedModule("lib.other", "lib.other.f");

    /** Every text a position can be in, made the way every caller makes one. */
    private static List<Placement> texts() {
        return List.of(
                Placement.aFileOfThisCompile(new SourceId("model.sou")),
                Placement.aTextWithNoIdentity(),
                Placement.whatAModulePublished(LIB));
    }

    /** Every state, which is every text with the code written at it and with code copied into it. */
    private static List<Placement> every() {
        List<Placement> all = new ArrayList<>(texts());
        texts().forEach(text -> all.add(text.standingInFor(new DeclaringCode(OTHER))));
        return all;
    }

    /** The two answers, as the pair that says which state a placement is in. */
    private record State(Class<?> text, Class<?> code) {}

    private static State stateOf(Placement placement) {
        return new State(placement.text().getClass(), placement.code().getClass());
    }

    @Test
    void everyPairOfAnswersIsAStateAndNoTwoStatesGiveTheSamePair() {
        Map<State, Placement> byState = new LinkedHashMap<>();
        for (Placement placement : every()) {
            Placement was = byState.put(stateOf(placement), placement);
            assertTrue(was == null, () -> "two states answer the two questions the same way, so one"
                    + " of them is the other written differently: " + was + " and " + placement);
        }

        Set<Class<?>> textKinds = new LinkedHashSet<>();
        texts().forEach(text -> textKinds.add(text.text().getClass()));
        assertEquals(Set.of(Placement.Text.class.getPermittedSubclasses()), textKinds,
                "every text a position can be in is one a caller can make");
        assertEquals(textKinds.size() * Placement.CodeOrigin.class.getPermittedSubclasses().length,
                byState.size(), "the states are the product of the two questions");
    }

    /**
     * A splice keeps the text and replaces the code.
     *
     * <p>Said of the operation rather than of the six results, so a state added later is held to it
     * without anybody having written down what its answer should be. This is what the first version
     * of this design got wrong: with one boolean for both questions, a splice into a text nobody
     * named had nowhere to land and rewrote which text the position was in — a snippet became a
     * module's published text.
     */
    @Test
    void aSpliceKeepsTheTextAndReplacesTheCode() {
        for (Placement before : every()) {
            Placement after = before.standingInFor(new DeclaringCode(LIB));

            assertTrue(before.isTheSameTextAs(after),
                    () -> "a body is spliced into the text the caller is in, and that text is the"
                            + " same text afterwards: " + before);
            assertEquals(before.text(), after.text(), () -> "in every component of it: " + before);
            assertEquals(LIB, after.codeIsWrittenIn(),
                    () -> "and what it now carries is what the splice was told: " + before);
        }
    }

    /**
     * A splice replaces what a position already carried and does not compose with it.
     *
     * <p>A position already carrying copied code is carrying the copy this one is nested inside, and
     * the body a position belongs to is the innermost one it came out of — so the outer answer is
     * about something else. {@link Placement#standingInFor} takes a declaration and not a placement
     * for that reason, and this is the same statement from outside.
     */
    @Test
    void aSecondSpliceSaysWhatTheSecondSpliceSaid() {
        for (Placement before : every()) {
            Placement twice = before.standingInFor(new DeclaringCode(LIB))
                    .standingInFor(new DeclaringCode(OTHER));

            assertEquals(OTHER, twice.codeIsWrittenIn(),
                    () -> "the body this position belongs to is the one copied in last: " + before);
        }
    }

    /**
     * A published text is the same text however a reading reached it.
     *
     * <p>What a reader here writes for the code is a fact about the reading — two imports reach one
     * module by two names as easily as one — so a text carrying it would be two texts, and the same
     * module would stop being the same text depending on which import found it. The route lives on
     * what a position carries, which is the other question.
     */
    @Test
    void aPublishedTextIsTheSameTextHoweverAReadingReachedIt() {
        assertEquals(Placement.whatAModulePublished(new SourceProvenance.APublishedModule("lib.rule")),
                Placement.whatAModulePublished(LIB),
                "the module is which text it is; the name it was reached by is not");
        assertTrue(Placement.whatAModulePublished(LIB).at(1, 1).isInTheSameTextAs(
                        Placement.whatAModulePublished(
                                new SourceProvenance.APublishedModule("lib.rule", "alias.atLeast"))
                                .at(9, 9)),
                "and two readings of it are reading the same text");
    }

    /** Which file a position is read from is the text's answer, whatever was copied into it. */
    @Test
    void whichFileThisIsReadFromIsDecidedByTheTextAlone() {
        for (Placement text : texts()) {
            assertEquals(text.quotedFrom(),
                    text.standingInFor(new DeclaringCode(LIB)).quotedFrom(),
                    () -> "a splice moves code and not files: " + text);
        }
    }

    /**
     * Where the code is written is read off both, and off the text where nothing was copied in.
     *
     * <p>Code copied here is written where it came from. Code of its own is written wherever this
     * text is — which is a module, for a text a module published, and is nothing to state for a text
     * a reader has in front of them. That last is why a published text's positions are not a special
     * case of being copied: nothing moved them.
     */
    @Test
    void whereTheCodeIsWrittenIsReadOffBoth() {
        Placement published = Placement.whatAModulePublished(LIB);
        assertEquals(LIB.asDeclared(), published.codeIsWrittenIn(),
                "code in a module's own text is written in that module, as the declaration knows it"
                        + " rather than as whichever reading found the text wrote it");
        assertEquals(OTHER, published.standingInFor(new DeclaringCode(OTHER)).codeIsWrittenIn(),
                "and a body spliced into that text is written where it came from");

        for (Placement held : List.of(Placement.aFileOfThisCompile(new SourceId("model.sou")),
                Placement.aTextWithNoIdentity())) {
            assertNull(held.codeIsWrittenIn(),
                    "a text a reader is looking at has no elsewhere to name");
        }
    }

    private static void assertNull(Object value, String message) {
        assertTrue(value == null, () -> message + ", and it named " + value);
    }

    /**
     * A citation with nowhere to point always says where the code is.
     *
     * <p>Not a rule about how many arms there are — a rule about what a report may leave a reader
     * with. There is nowhere to point exactly where this compile has no file for the text, and having
     * no file for it is knowing which module published it, so "nothing to point at and nothing to
     * say instead" is not a state a report can be in. That was the drop this whole family of defects
     * started as.
     */
    @Test
    void aCitationWithNowhereToPointSaysWhereTheCodeIs() {
        for (Placement placement : every()) {
            Citation citation = placement.cite(placement.at(3, 5));
            switch (citation) {
                case Citation.Written w -> assertNotNull(w.at(), "a place to point at");
                case Citation.Unplaced u -> assertNotNull(u.at(), "a position to offer the caller");
                case Citation.Reached r -> assertNotNull(r.at(), "a place to point at");
                case Citation.UnplacedElsewhere u ->
                        assertNotNull(u.at(), "a position to offer the caller");
                case Citation.OutOfSight out -> assertNotNull(out.provenance(),
                        "what a reader is told in place of being pointed anywhere");
            }
        }
    }

    /** And every one of those arms is reached, so the switch above is not five names over one case. */
    @Test
    void everyArmOfACitationIsReachedBySomeState() {
        Set<Class<?>> cited = new LinkedHashSet<>();
        every().forEach(placement -> cited.add(placement.cite(placement.at(3, 5)).getClass()));

        assertEquals(5, cited.size(), () -> "six states, five things a report can say: " + cited);
    }

    /**
     * Neither question is published, and neither is what a position carries.
     *
     * <p>The two questions are what every consumer used to answer privately, out of a source
     * identity that could be null. A predicate for either, or an accessor for the provenance, would
     * be that again under a name that reads like an improvement — so what this refuses is a public
     * method that could answer one, by what it returns rather than by what it is called.
     */
    @Test
    void noneOfThisIsReadableFromOutsideThisPackage() {
        List<Class<?>> types = new ArrayList<>(List.of(Placement.class, Placement.Text.class,
                Placement.CodeOrigin.class));
        types.addAll(List.of(Placement.Text.class.getPermittedSubclasses()));
        types.addAll(List.of(Placement.CodeOrigin.class.getPermittedSubclasses()));

        for (Class<?> type : types) {
            if (type != Placement.class) {
                // Held to being unnameable rather than to having no public members. A record's
                // accessors are public and an interface's methods are, so what keeps them out of
                // reach is the type itself, and that is the thing to check.
                assertFalse(Modifier.isPublic(type.getModifiers()),
                        () -> "a component a caller can name is one it can switch over: "
                                + type.getName());
                continue;
            }
            for (Method method : type.getDeclaredMethods()) {
                if (!Modifier.isPublic(method.getModifiers()) || method.isSynthetic()
                        || method.getName().equals("equals")) {
                    continue;
                }
                assertFalse(ANSWERS_A_QUESTION.contains(method.getReturnType()),
                        () -> "a placement answers no question a reader may ask, and this one"
                                + " answers " + method.getReturnType().getSimpleName() + ": "
                                + type.getSimpleName() + "." + method.getName());
            }
        }
    }

    /** What the two questions are answered with, and what a position carries. Read by what a method
     *  returns rather than by what it is called: a predicate renamed is the same leak. */
    private static final Set<Class<?>> ANSWERS_A_QUESTION =
            Set.of(boolean.class, Boolean.class, SourceId.class, SourceProvenance.class);
}
