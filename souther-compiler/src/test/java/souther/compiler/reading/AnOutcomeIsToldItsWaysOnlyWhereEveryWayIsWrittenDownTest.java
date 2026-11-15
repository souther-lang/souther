package souther.compiler.reading;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.core.Core;
import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.flow.Arrival;
import souther.compiler.flow.Completeness;
import souther.compiler.flow.Paths;
import souther.compiler.flow.Provenance;
import souther.compiler.flow.Truth;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a row has to be to settle a decision one way is the union of the ways that reach it, so an
 * outcome is told those ways only where every one of them was written down whole.
 *
 * <p>One way the naming could not write is a part of the region that the others do not state. Told
 * the rest as if they were all, the outcome would be narrower than the rows that settle it, and a
 * combination with a decision on those rows would not exist.
 */
class AnOutcomeIsToldItsWaysOnlyWhereEveryWayIsWrittenDownTest {

    private static final String MODEL = """
            module m

            behavior pick : (flag: Bool) -> Int
            let pick (flag) = if flag then 1 else 2
            """;

    @Test
    void twoWaysWrittenWholeAreWhatARowHasToBe() {
        Fixture fixture = new Fixture();

        Meetings.Reached reached = Meetings.outcomesFrom(List.of(
                fixture.reaching(Completeness.COMPLETE, 0),
                fixture.reaching(Completeness.COMPLETE, 1)));

        assertEquals(1, reached.outcomes().size(),
                "two ways a run is not seen to tell apart are one outcome");
        assertEquals(2, waysOf(reached.outcomes().getFirst()).size(), "and it is told both");
        assertTrue(reached.known(), "and no way of it is one no run is seen taking");
    }

    @Test
    void aWayNotWrittenWholeLeavesTheOutcomeOfferedAndItsRegionUnsaid() {
        Fixture fixture = new Fixture();

        Meetings.Reached reached = Meetings.outcomesFrom(List.of(
                fixture.reaching(Completeness.COMPLETE, 0),
                fixture.reaching(Completeness.PARTIAL, 1)));

        assertEquals(1, reached.outcomes().size(),
                "the outcome is reached whole by one way, so it is offered");
        assertTrue(waysOf(reached.outcomes().getFirst()).isEmpty(),
                "but not told the one way: the other is rows it does not state");
    }

    /**
     * What identifies an outcome is what a run is seen doing, so an outcome the ways to which could
     * not be written whole is still one where a run is seen at the arm.
     */
    @Test
    void anOutcomeASeenArmIdentifiesIsOfferedWhateverCouldBeWrittenOfTheWaysToIt() {
        Fixture fixture = new Fixture();

        Meetings.Reached reached = Meetings.outcomesFrom(List.of(
                fixture.reaching(Completeness.PARTIAL, 0)));

        assertEquals(1, reached.outcomes().size(), "the arm a run is seen at is the outcome");
        assertTrue(waysOf(reached.outcomes().getFirst()).isEmpty(), "with its region unsaid");
        assertTrue(reached.known(), "and it is no way that nobody is seen taking");
    }

    /**
     * A way that is neither written whole nor seen at an arm is an outcome of the operand all the
     * same, which no run is seen taking: it is said, and not dropped as if there were none.
     */
    @Test
    void anOutcomeNothingASeenArmOrAWholeWayIdentifiesIsSaidAndNotDropped() {
        Fixture fixture = new Fixture();

        Meetings.Reached reached = Meetings.outcomesFrom(List.of(
                fixture.reaching(Completeness.COMPLETE, 0),
                fixture.unseen()));

        assertEquals(1, reached.outcomes().size(), "the outcome that can be seen is offered");
        assertEquals(1, reached.unseen(), "and the one that cannot is said");
    }

    /**
     * What this reading will not hold apart is not none: no run arriving at a value is an empty list
     * of ways, and ways it will not enumerate is a different answer.
     */
    @Test
    void waysThisReadingWillNotHoldApartAreNotNoWays() {
        Meetings.Reached none = Meetings.reachedBy(new Paths.Held<>(List.of()));
        Meetings.Reached beyond = Meetings.reachedBy(new Paths.Beyond<>());

        assertTrue(none.known() && none.outcomes().isEmpty(), "a value no run arrives at");
        assertTrue(beyond.unenumerated() && beyond.outcomes().isEmpty(),
                "a value settled more ways than are held apart");
        assertTrue(beyond.mayVary() && !none.mayVary(), "which may be a decision, as none is not");
    }

    /**
     * An operand nothing is known of may be a decision, so a meeting with another that is one
     * cannot be named, and is said and not offered over the operand that is known.
     */
    @Test
    void anOperandOfWhichNothingIsKnownTakesTheMeetingOutOfBeingOffered() {
        Fixture fixture = new Fixture();
        Meetings.Reached two = Meetings.outcomesFrom(List.of(
                fixture.reachingArm(0), fixture.reachingArm(1)));
        Meetings.Reached one = Meetings.outcomesFrom(List.of(fixture.reachingArm(0)));
        Meetings.Reached unknown = Meetings.Reached.NOT_ENUMERATED;

        assertEquals(2, two.outcomes().size(), "two outcomes are a decision");
        assertEquals(WhyNotJoined.AN_OPERAND_HAS_MORE_WAYS_THAN_ARE_READ,
                Meetings.whyNotOffered(List.of(two, unknown)), "with one that is a decision");
        assertEquals(WhyNotJoined.AN_OPERAND_HAS_MORE_WAYS_THAN_ARE_READ,
                Meetings.whyNotOffered(List.of(unknown, unknown)),
                "with another of which nothing is known");
        assertNull(Meetings.whyNotOffered(List.of(one, unknown)),
                "but not with one that is a single way: that is no second decision");
    }

    /**
     * Two operands of which the same is not known are not one decision named twice. What is known of
     * both is all the same, and that is no word on whether they are the same choice.
     */
    @Test
    void operandsNothingIsKnownOfAreNotMergedForBeingAlike() {
        Fixture fixture = new Fixture();
        Meetings.Reached known = Meetings.outcomesFrom(List.of(
                fixture.reaching(Completeness.COMPLETE, 0)));

        assertEquals(2, Meetings.distinct(List.of(Meetings.Reached.NOT_ENUMERATED,
                Meetings.Reached.NOT_ENUMERATED)).size(), "two that cannot be read stay two");
        assertEquals(2, Meetings.distinct(List.of(new Meetings.Reached(List.of(), 2, false),
                new Meetings.Reached(List.of(), 2, false))).size(),
                "and so do two with ways unseen");
        assertEquals(1, Meetings.distinct(List.of(known, known)).size(),
                "while one that is all known and used twice is the one decision");
    }

    private static List<List<Condition>> waysOf(Outcome outcome) {
        return ((Condition.Arm) outcome.holds().getFirst().constrains()).comesOutBy();
    }

    /** Arms of one fork, standing for the outcome and for conditions that reach it. */
    private static final class Fixture {

        private final ControlPlace.Arm[] arms;

        Fixture() {
            Compilation compilation = ACompiledModel.answered(MODEL);
            Bodies.Elaborated checked = compilation.db()
                    .ask(new Bodies.Checked(compilation.modules().get(0))).value();
            arms = checked.plan().armsOf(forkIn(checked.behaviorBodies().get("pick")));
        }

        /** An arrival at the outcome that is the arm {@code arm} was taken, by a way written as
         *  the condition that arm {@code way} was taken. */
        Arrival<Outcome> reaching(Completeness completeness, int way) {
            Outcome seen = outcomeOf(0);
            Outcome path = outcomeOf(way);
            return new Arrival<>(Truth.FALSE, new Provenance<>(path, completeness, List.of(), seen));
        }

        /** An arrival at the outcome that is the arm {@code arm}, written whole as that arm. */
        Arrival<Outcome> reachingArm(int arm) {
            Outcome outcome = outcomeOf(arm);
            return new Arrival<>(Truth.FALSE,
                    new Provenance<>(outcome, Completeness.COMPLETE, List.of(), null));
        }

        /** An arrival written down in part and seen at no arm: a path of nothing named, which no run
         *  is seen doing. */
        Arrival<Outcome> unseen() {
            Outcome nothing = new Outcome(List.of());
            return new Arrival<>(Truth.FALSE,
                    new Provenance<>(nothing, Completeness.PARTIAL, List.of(), null));
        }

        private Outcome outcomeOf(int arm) {
            return new Outcome(List.of(new Decision(
                    new Condition.Arm(arms[arm].arm(), Optional.empty()),
                    ControlClaim.of(arms[arm]).orElseThrow())));
        }

        private static Core forkIn(Core body) {
            List<Core> found = new ArrayList<>();
            collect(body, found);
            return found.getFirst();
        }

        private static void collect(Core e, List<Core> found) {
            if (e instanceof Core.If) {
                found.add(e);
            }
            Core.forEachChild(e, child -> collect(child, found));
        }
    }
}
