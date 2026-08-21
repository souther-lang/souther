package souther.compiler.interaction;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.InputDomain;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A way in is held to the way in above it, and one that contradicts it is no path.
 *
 * <p>What a group carries is one conjunction, and every decision on it was settled by one run. Two
 * of them settling one decision opposite ways describes no run at all — so the walk does not go
 * that way, rather than going and leaving what it finds to be thrown out further on.
 *
 * <p>Which matters beyond the rows: how many ways in a position is read under is what bounds the
 * reading, and a way nothing could take would spend a share of that bound and push a way something
 * could take out of it.
 */
class AWayInIsHeldToWhatAlreadyHeldTest {

    /** A meeting under two arms of one decision that cannot both be taken. */
    private static final String CONTRADICTED = """
            module example.contradicted

            data Tier = Bronze | Silver

            behavior fee : (tier: Tier, a: Bool, b: Bool) -> Int

            let fee (tier, a, b) =
                match tier with
                    | Bronze ->
                        match tier with
                            | Bronze -> 0
                            | Silver -> (if a then 1 else 0) + (if b then 10 else 0)
                    | Silver -> 0
            """;

    /** The same meeting under the arm of that decision that agrees with the one above it. */
    private static final String AGREED = """
            module example.agreed

            data Tier = Bronze | Silver

            behavior fee : (tier: Tier, a: Bool, b: Bool) -> Int

            let fee (tier, a, b) =
                match tier with
                    | Bronze ->
                        match tier with
                            | Bronze -> (if a then 1 else 0) + (if b then 10 else 0)
                            | Silver -> 0
                    | Silver -> 0
            """;

    /** A meeting in the arm of a condition that comes out the same way for every row. */
    private static final String NEVER_REACHED = """
            module example.neverreached

            behavior fee : (a: Bool, b: Bool) -> Int

            let fee (a, b) =
                if true
                    then 0
                    else (if a then 1 else 0) + (if b then 10 else 0)
            """;

    /** The same, in the arm every row does take. */
    private static final String ALWAYS_REACHED = """
            module example.alwaysreached

            behavior fee : (a: Bool, b: Bool) -> Int

            let fee (a, b) =
                if true
                    then (if a then 1 else 0) + (if b then 10 else 0)
                    else 0
            """;

    private static List<Interaction> read(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get(behavior);
        assertNotNull(body, "the behavior under test has a body");
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get(behavior);
        return Interactions.of(body, CoverageSites.of(checked.behaviorBodies()), inputs, symbols);
    }

    /**
     * A group under two arms of one decision that disagree is not offered.
     *
     * <p>No row settles the same decision both ways, so there is no row to offer this to. Left in,
     * it reads as a group something could cover and takes its turn among the ones that can be.
     */
    @Test
    void aMeetingUnderTwoArmsOfOneDecisionThatDisagreeIsNoPath() {
        assertEquals(List.of(), read(CONTRADICTED, "fee"),
                "one run does not match the same value as two different cases");
    }

    /**
     * The same meeting where the two arms agree, which is one decision and two places.
     *
     * <p>No row takes the inner arm without the outer one, so reading the second naming of the
     * decision as a contradiction would take away the only path there is. What the way in asks of
     * the input is one thing; what a run that took it is seen to have done is both arms, and both
     * are true of it.
     */
    @Test
    void aMeetingUnderTwoArmsOfOneDecisionThatAgreeIsOnePath() {
        List<Interaction> found = read(AGREED, "fee");

        assertEquals(1, found.size(), "the two charges meet once: " + found);
        assertEquals(List.of("tier=Bronze"),
                found.get(0).reach().stream().map(Object::toString).distinct().toList(),
                "one thing is asked of the input to get there: " + found);
        assertEquals(2, found.get(0).reachClaims().size(),
                "and a run that got there went through both arms: " + found);
    }

    /**
     * An arm no row reaches is not walked, which is not the same as an arm this reading cannot
     * name a way in to.
     *
     * <p>The first has an answer — there are no ways to that value and the list of them is empty —
     * and the second has none. Told apart, the arm nothing reaches costs nothing; run together
     * under one absent answer, it would be read under the arm itself, and the group in it offered
     * to a row that can never be written.
     */
    @Test
    void anArmNoRowReachesIsNotWalked() {
        assertEquals(List.of(), read(NEVER_REACHED, "fee"),
                "nothing settles the condition the way this arm is taken on");
    }

    /** The arm every row takes, which is reached under nothing rather than under an arm. */
    @Test
    void anArmEveryRowTakesIsReachedUnderNothing() {
        List<Interaction> found = read(ALWAYS_REACHED, "fee");

        assertEquals(1, found.size(), "the two charges meet once: " + found);
        assertEquals(List.of(), found.get(0).reach(),
                "and getting to them asks nothing of the inputs: " + found);
    }
}
