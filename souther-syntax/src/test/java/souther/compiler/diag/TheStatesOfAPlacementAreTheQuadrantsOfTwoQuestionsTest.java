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
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@link Placement} has the states two questions have answers, and not a number of states somebody
 * counted.
 *
 * <p>Whether this compilation can show a reader the text, and whether the code the position names is
 * written at it. Two questions with two answers each, so four states, and every one of them is a
 * quadrant rather than a kind of text that happened to turn up. The distinction is what makes a fifth
 * arm answerable: one that fills a quadrant already filled is one of these four written wrongly, and
 * one that cannot answer both questions is a claim that a third question exists, which is a thing to
 * argue for rather than to add.
 *
 * <p>This is not type safety. The compiler already refuses a fifth arm that does not implement what
 * the class declares. What this holds is the other half — that the sealed hierarchy is the state
 * space somebody designed, and has not drifted into being a list.
 *
 * <p>The arms are not named here. Naming them would make this a copy of the declaration, green on the
 * day a fifth was added and left off the copy. What is named is the two questions, and the arms are
 * reached the way every caller reaches them: through the factories and through the one operation that
 * makes the fourth.
 */
class TheStatesOfAPlacementAreTheQuadrantsOfTwoQuestionsTest {

    /** Where the code is, for the arms that say it is written somewhere else. */
    private static final SourceProvenance ELSEWHERE =
            new SourceProvenance.APublishedModule("lib.rule", "lib.rule.atLeast");

    /**
     * Every placement a caller can make, which is every placement there is.
     *
     * <p>Through the published ways of making one. A test that reached in and built each arm would
     * be saying the arms exist; this says they are what a compile actually holds, so an arm nothing
     * can reach fails here rather than sitting unread.
     */
    private static List<Placement> reachable() {
        List<Placement> made = new ArrayList<>(List.of(
                Placement.aFileOfThisCompile(new SourceId("model.sou")),
                Placement.aTextWithNoIdentity(),
                Placement.whatAModulePublished(ELSEWHERE)));
        Placement declaring = Placement.whatAModulePublished(ELSEWHERE);
        for (Placement one : List.copyOf(made)) {
            made.add(one.standingInFor(declaring));
        }
        return made;
    }

    /** The two answers, as the pair that says which quadrant a placement is in. */
    private record Quadrant(boolean named, boolean codeIsHere) {}

    private static Quadrant quadrantOf(Placement placement) {
        return new Quadrant(placement.namedByThisCompile(), placement.codeIsWrittenHere());
    }

    @Test
    void everyArmFillsAQuadrantAndNoTwoFillTheSameOne() {
        Map<Quadrant, Class<?>> byQuadrant = new LinkedHashMap<>();
        for (Placement placement : reachable()) {
            Class<?> was = byQuadrant.put(quadrantOf(placement), placement.getClass());
            assertTrue(was == null || was == placement.getClass(),
                    () -> "two arms answer the two questions the same way, so one of them is the"
                            + " other written differently: " + was + " and " + placement.getClass());
        }

        Set<Quadrant> everyQuadrant = new LinkedHashSet<>();
        for (boolean named : new boolean[] {true, false}) {
            for (boolean here : new boolean[] {true, false}) {
                everyQuadrant.add(new Quadrant(named, here));
            }
        }
        assertEquals(everyQuadrant, byQuadrant.keySet(),
                "a state space of two questions has a state for each pair of answers");
    }

    /** And the arms are exactly those states: one nothing can reach is one nothing has thought
     *  about, and one reached twice is the count above being read off too few of them. */
    @Test
    void theArmsAreTheStatesAndEveryOneOfThemIsReachable() {
        Set<Class<?>> reached = new LinkedHashSet<>();
        reachable().forEach(placement -> reached.add(placement.getClass()));

        assertEquals(Set.of(Placement.class.getPermittedSubclasses()), reached,
                "every arm is one a caller can make, and every one a caller can make is an arm");
    }

    /**
     * What a splice does to a place: the first question is kept and the second is answered elsewhere.
     *
     * <p>Said of the operation rather than of the four results. A fifth arm implementing it wrongly
     * fails here without anybody having listed what its answer should be.
     */
    @Test
    void standingInForKeepsWhetherTheTextIsNamedAndMovesWhereTheCodeIs() {
        Placement declaring = Placement.whatAModulePublished(ELSEWHERE);
        for (Placement before : reachable()) {
            Placement after = before.standingInFor(declaring);

            assertEquals(before.namedByThisCompile(), after.namedByThisCompile(),
                    () -> "a body is spliced into the text the caller is in, and that text is the"
                            + " same text afterwards: " + before);
            assertFalse(after.codeIsWrittenHere(),
                    () -> "what a copy stands in for is written where it was copied from: " + before);
            assertEquals(ELSEWHERE, after.codeIsWrittenIn(),
                    () -> "and where that is, is what the splice was told: " + before);
        }
    }

    /**
     * A splice replaces what a place stood in for and does not compose with it.
     *
     * <p>A position already standing in is standing in for the copy this one is nested inside, and
     * the body a position belongs to is the innermost one it was copied out of. So the outer answer
     * is about something else. The operation takes a provenance and not a placement for that reason,
     * and this is the same statement from outside.
     */
    @Test
    void standingInForTwiceSaysWhatTheSecondSpliceSaid() {
        SourceProvenance inner = new SourceProvenance.APublishedModule("lib.inner", "lib.inner.f");
        for (Placement before : reachable()) {
            Placement twice = before.standingInFor(Placement.whatAModulePublished(ELSEWHERE))
                    .standingInFor(Placement.whatAModulePublished(inner));

            assertEquals(inner, twice.codeIsWrittenIn(),
                    () -> "the body this position belongs to is the one copied in last: " + before);
        }
    }

    /**
     * Neither question is published, and neither is what a place stands in for.
     *
     * <p>The two questions are what every consumer used to answer privately, out of a source
     * identity that could be null. A predicate for either of them, or an accessor for the
     * provenance, would be that again under a name that reads like an improvement — so what this
     * refuses is a public method that could answer one, by what it returns rather than by what it is
     * called.
     *
     * <p>The arms as well as the class. An arm that is reachable by name outside this package is one
     * a {@code switch} can be written over, and a switch outside here is a consumer classifying a
     * place for itself.
     */
    @Test
    void noneOfThisIsReadableFromOutsideThisPackage() {
        List<Class<?>> types = new ArrayList<>(List.of(Placement.class));
        types.addAll(List.of(Placement.class.getPermittedSubclasses()));

        for (Class<?> type : types) {
            if (type != Placement.class) {
                assertFalse(Modifier.isPublic(type.getModifiers()),
                        () -> "an arm a caller can name is an arm a caller can switch over: "
                                + type.getName());
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

    /** What the two questions are answered with, and what a place stands in for. Read by what a
     *  method returns rather than by what it is called: a predicate renamed is the same leak. */
    private static final Set<Class<?>> ANSWERS_A_QUESTION =
            Set.of(boolean.class, Boolean.class, SourceId.class, SourceProvenance.class);
}
