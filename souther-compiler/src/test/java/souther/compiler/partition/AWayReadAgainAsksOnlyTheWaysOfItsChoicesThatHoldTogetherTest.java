package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.partition.WaysReadAgain.anElement;
import static souther.compiler.partition.WaysReadAgain.oneOf;
import static souther.compiler.partition.WaysReadAgain.truth;
import static souther.compiler.partition.WaysReadAgain.x;

/**
 * A way read again for a relation on {@code x} and {@code y} asks the ways of taking its choices
 * together that may hold together, and reads a choice as less only where every value of the
 * numbers a way of them leaves is one a row past them takes.
 */
class AWayReadAgainAsksOnlyTheWaysOfItsChoicesThatHoldTogetherTest {

    /** The lines both choices part {@code x} by, whose runs squared are more ways than a way is
     *  looked along with. */
    private static final int LINES = 4;

    /** A number the relation reads, bounded {@code rel threshold}. */
    private interface Bound {
        OnTheWay of(long weight, Rel rel, long threshold);
    }

    /**
     * A choice parting a number at each of {@link #LINES}, asking apart of each run that the truth
     * numbered as the run holds and the next does not, which every choice made here asks of
     * alike. No value meets what every run asks at once, so the ways of taking the choices
     * together are asked one by one.
     */
    private static OnTheWay parting(int at, Bound number) {
        return parting(at, number, LINES);
    }

    /** The same at each of {@code lines} lines. */
    private static OnTheWay parting(int at, Bound number, int lines) {
        List<List<OnTheWay>> runs = new ArrayList<>();
        for (int run = 0; run <= lines; run++) {
            List<OnTheWay> asked = new ArrayList<>(theRun(run, number, lines));
            asked.addAll(askedApart(run));
            runs.add(asked);
        }
        return oneOf(at, runs);
    }

    /**
     * The same choice with each run's lines written only inside a choice of its own halves, as a
     * lookup in a table writes them: the run is one half or the other.
     */
    private static OnTheWay partingInside(int at, Bound number) {
        List<List<OnTheWay>> runs = new ArrayList<>();
        for (int run = 0; run <= LINES; run++) {
            List<OnTheWay> below = new ArrayList<>(theRun(run, number, LINES));
            below.add(number.of(1, Rel.LT, run * 10L + 5));
            List<OnTheWay> above = new ArrayList<>(theRun(run, number, LINES));
            above.add(number.of(1, Rel.GE, run * 10L + 5));
            List<OnTheWay> asked = new ArrayList<>();
            asked.add(oneOf(at * 100 + run, List.of(below, above)));
            asked.addAll(askedApart(run));
            runs.add(asked);
        }
        return oneOf(at, runs);
    }

    /** A choice parting a number at each of {@link #LINES}, asking apart of each run that the
     *  truth {@code c} holds where the run is numbered evenly and not where it is not. */
    private static OnTheWay partingAskingOneTruth(int at, Bound number) {
        List<List<OnTheWay>> runs = new ArrayList<>();
        for (int run = 0; run <= LINES; run++) {
            List<OnTheWay> asked = new ArrayList<>(theRun(run, number, LINES));
            asked.add(truth("c", run % 2 == 0));
            runs.add(asked);
        }
        return oneOf(at, runs);
    }

    /** The lines either side of the run numbered {@code run} of those {@code lines} lines leave. */
    private static List<OnTheWay> theRun(int run, Bound number, int lines) {
        List<OnTheWay> out = new ArrayList<>();
        if (run > 0) {
            out.add(number.of(1, Rel.GE, run * 10L));
        }
        if (run < lines) {
            out.add(number.of(1, Rel.LT, (run + 1) * 10L));
        }
        return out;
    }

    /** What the run numbered {@code run} asks apart. */
    private static List<OnTheWay> askedApart(int run) {
        return List.of(truth("c" + run, true), truth("c" + (run + 1), false));
    }

    /**
     * Two choices parting {@code x} by the same lines take their runs together only where they
     * agree, so the ways of them are as many as the runs and not their square, and each is met.
     */
    @Test
    void choicesPartingOneNumberByTheSameLinesAreAskedAlongTheRunsTheyAgreeOn() {
        AWayReadForARelation.ReadAgain again = WaysReadAgain.readAgain(
                List.of(parting(1, WaysReadAgain::x), parting(2, WaysReadAgain::x)));

        assertFalse(again.stoppedAt().contains(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG),
                () -> "the ways were not more than a way is looked along with: "
                        + again.stoppedAt());
        assertTrue(again.as().isPresent(), "and the way is read as less for the relation");
    }

    /**
     * Two choices parting {@code x} by so many lines that every run of one taken in beside every
     * run of the other is more than a way's choices are looked at with: each run is taken in
     * beside the runs of its own line alone, so the looking stops short of that figure.
     */
    @Test
    void choicesPartingOneNumberByManyLinesAreLookedAtLineByLine() {
        int lines = CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT.maximum() / 20;
        AWayReadForARelation.ReadAgain again = WaysReadAgain.readAgain(List.of(
                parting(1, WaysReadAgain::x, lines), parting(2, WaysReadAgain::x, lines)));

        assertFalse(again.stoppedAt().contains(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT),
                () -> "the alternatives looked at were fewer than the figure: "
                        + again.stoppedAt());
    }

    /** The same where the lines are written only inside a choice in each alternative. */
    @Test
    void choicesPartingOneNumberInsideTheirAlternativesAreAskedAlongTheRunsTheyAgreeOn() {
        AWayReadForARelation.ReadAgain again = WaysReadAgain.readAgain(List.of(
                partingInside(1, WaysReadAgain::x), partingInside(2, WaysReadAgain::x)));

        assertFalse(again.stoppedAt().contains(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG),
                () -> "the ways were not more than a way is looked along with: "
                        + again.stoppedAt());
        assertTrue(again.as().isPresent(), "and the way is read as less for the relation");
    }

    /**
     * A choice of more runs than a way is looked along with, and after it one parting the first
     * run in two, both asking apart of the one truth {@code c} — every run of the first that it
     * is held at and every other that it is not, so that no value meets what all the runs ask at
     * once. The ways of the first alone are past the figure, and the second closes all but the two
     * inside its run: the ways looked along are those left once every choice is taken.
     */
    @Test
    void waysPastTheFigureBeforeTheLastChoiceAreCountedWhereItLeavesThem() {
        int lines = CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum();
        List<List<OnTheWay>> runs = new ArrayList<>();
        for (int run = 0; run <= lines; run++) {
            List<OnTheWay> asked = new ArrayList<>(theRun(run, WaysReadAgain::x, lines));
            asked.add(truth("c", run % 2 == 0));
            runs.add(asked);
        }
        OnTheWay halves = oneOf(2, List.of(
                List.of(x(1, Rel.LT, 5), truth("c", true)),
                List.of(x(1, Rel.GE, 5), x(1, Rel.LT, 10), truth("c", true))));
        AWayReadForARelation.ReadAgain again = WaysReadAgain.readAgain(
                List.of(oneOf(1, runs), halves));

        assertFalse(again.stoppedAt().contains(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG),
                () -> "the ways were not more than a way is looked along with: "
                        + again.stoppedAt());
        assertTrue(again.as().isPresent(), "and the way is read as less for the relation");
    }

    /**
     * Control: parting {@code x} and {@code y}, every run of one holds with every run of the
     * other, and the ways are the product. Each asks apart of the one truth {@code c}, held at
     * the even runs and not at the odd, which only a walk answers: the ways looked along are more
     * than a way is.
     */
    @Test
    void choicesPartingTwoNumbersAreAskedAlongTheProductOfTheirRuns() {
        AWayReadForARelation.ReadAgain again = WaysReadAgain.readAgain(List.of(
                partingAskingOneTruth(1, WaysReadAgain::x),
                partingAskingOneTruth(2, WaysReadAgain::y)));

        assertTrue(again.as().isEmpty(), () -> "nothing is read as less: " + again.as());
        assertTrue(again.stoppedAt().contains(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG),
                () -> "stopped at the ways a way is looked along with: " + again.stoppedAt());
    }

    /**
     * Under {@code (x <= 0 && t || x >= 10 && !t)} and {@code (x <= 3 && !t || x >= 7 && t)} no
     * row takes both, and the ways of them {@code x} reaches ask {@code t} both ways. Read as
     * less, the two would leave {@code x} at or below nought and at or above ten, which no row
     * holds: no way met holds those values, so neither is read as less.
     */
    @Test
    void aWayNoValueMeetsApartIsNotReadAsLessWhereNoWayMetHoldsItsValues() {
        AWayReadForARelation.ReadAgain again = WaysReadAgain.readAgain(List.of(
                oneOf(1, List.of(List.of(x(1, Rel.LE, 0), truth("t", true)),
                        List.of(x(1, Rel.GE, 10), truth("t", false)))),
                oneOf(2, List.of(List.of(x(1, Rel.LE, 3), truth("t", false)),
                        List.of(x(1, Rel.GE, 7), truth("t", true))))));

        assertTrue(again.as().isEmpty(), () -> "nothing is read as less: " + again.as());
    }

    /**
     * Under {@code (e < 0 && t || e >= 0 && s)} and {@code (e < -1 && s || e >= 1 && !t)}, where
     * {@code e} is an element of a list, a row may take the first of one and the second of the
     * other with one element below nought and another at one or above, as the walk of that way
     * says: the way asks {@code t} both ways, no way met asks less of the relation, and so
     * neither is read as less. Read as bounds on one value, the way would be closed and not
     * asked.
     */
    @Test
    void boundsOnAnElementAreNotReadAsBoundsOnOneValue() {
        AWayReadForARelation.ReadAgain again = WaysReadAgain.readAgain(List.of(
                oneOf(1, List.of(List.of(anElement(1, Rel.LT, 0), truth("t", true)),
                        List.of(anElement(1, Rel.GE, 0), truth("s", true)))),
                oneOf(2, List.of(List.of(anElement(1, Rel.LT, -1), truth("s", true)),
                        List.of(anElement(1, Rel.GE, 1), truth("t", false))))));

        assertTrue(again.as().isEmpty(), () -> "nothing is read as less: " + again.as());
    }

    /**
     * Under {@code (x >= 10 && t || x < 10 && u)} and
     * {@code (2 * x >= 20 && !t || 3 * x >= 30 && v || x < 10 && u)}, no value is {@code t} and
     * not, but every {@code x} at or above ten that way leaves is one a row takes with {@code v}
     * — the same bound written another way, which is the one form it is on.
     */
    @Test
    void aWayNoValueMeetsApartIsReadWhereAWayMetHoldsTheSameValuesWrittenAnotherWay() {
        AWayReadForARelation.ReadAgain again = WaysReadAgain.readAgain(List.of(
                oneOf(1, List.of(List.of(x(1, Rel.GE, 10), truth("t", true)),
                        List.of(x(1, Rel.LT, 10), truth("u", true)))),
                oneOf(2, List.of(List.of(x(2, Rel.GE, 20), truth("t", false)),
                        List.of(x(3, Rel.GE, 30), truth("v", true)),
                        List.of(x(1, Rel.LT, 10), truth("u", true))))));

        assertTrue(again.as().isPresent(), () -> "read as less: " + again.stoppedAt());
    }

    /**
     * Under {@code !t} and {@code (0 <= x < 20 && t || 0 <= x < 10 && u || 10 <= x < 20 && v)},
     * no value meets the first alternative apart, and no one way met holds every {@code x} it
     * leaves: the two others do between them, each with a value of its own.
     */
    @Test
    void aWayNoValueMeetsApartIsReadWhereTheWaysMetHoldItsValuesBetweenThem() {
        AWayReadForARelation.ReadAgain again = WaysReadAgain.readAgain(List.of(
                truth("t", false),
                oneOf(1, List.of(
                        List.of(x(1, Rel.GE, 0), x(1, Rel.LT, 20), truth("t", true)),
                        List.of(x(1, Rel.GE, 0), x(1, Rel.LT, 10), truth("u", true)),
                        List.of(x(1, Rel.GE, 10), x(1, Rel.LT, 20), truth("v", true))))));

        assertTrue(again.as().isPresent(), () -> "read as less: " + again.stoppedAt());
    }

    /**
     * Under {@code (x <= 0 && z <= 10 || x > 0 && z >= 20)} each alternative is met by a value of
     * {@code z} of its own where the declarations leave {@code z} every value from nought to a
     * hundred, its bounds given values with no walk: read as less. Where they are not shown to
     * leave it any, no value is shown, and nothing is read as less.
     */
    @Test
    void aWayOfBoundsIsMetOnlyByAValueTheDeclarationsLeave() {
        List<OnTheWay> way = List.of(oneOf(1, List.of(
                List.of(x(1, Rel.LE, 0), WaysReadAgain.z(1, Rel.LE, 10)),
                List.of(x(1, Rel.GT, 0), WaysReadAgain.z(1, Rel.GE, 20)))));

        AWayReadForARelation.ReadAgain left = WaysReadAgain.readAgainLeavingZ(way);
        AWayReadForARelation.ReadAgain notLeft = WaysReadAgain.readAgain(way);

        assertTrue(left.as().isPresent(), () -> "left values, read as less: " + left.stoppedAt());
        assertEquals(Optional.empty(), notLeft.as(), "left none, read as it is");
    }

    /**
     * Under {@code (x <= 0 && t || x > 0 && !t)}, read as less where nothing ties {@code t} to
     * {@code x}: each alternative is met by a value of its own, and between them they leave
     * {@code x} every value. Where a rule ties the two, which {@code t} a row holds turns on its
     * {@code x}, the truths bear on the relation, and nothing is read as less.
     */
    @Test
    void aWayIsReadAsLessOnlyWhereWhatItAsksApartIsTiedToNothingTheRelationReads() {
        List<OnTheWay> way = List.of(oneOf(1, List.of(
                List.of(x(1, Rel.LE, 0), truth("t", true)),
                List.of(x(1, Rel.GT, 0), truth("t", false)))));

        AWayReadForARelation.ReadAgain apart = WaysReadAgain.readAgain(way);
        AWayReadForARelation.ReadAgain tied =
                WaysReadAgain.readAgainTying(way, TermPath.of("t"));

        assertTrue(apart.as().isPresent(), () -> "apart, read as less: " + apart.stoppedAt());
        assertEquals(Optional.empty(), tied.as(), "tied, read as it is");
    }

    /**
     * A choice whose alternatives between them leave {@code x} every value comes to nothing for
     * the relation and is left off the way read again; one leaving the values between nought
     * and ten out stays on it, and nothing is read as less.
     */
    @Test
    void aChoiceIsLeftOffOnlyWhereItsAlternativesLeaveEveryValue() {
        AWayReadForARelation.ReadAgain every = WaysReadAgain.readAgain(List.of(
                oneOf(1, List.of(List.of(x(1, Rel.LE, 0)), List.of(x(1, Rel.GT, 0))))));
        AWayReadForARelation.ReadAgain apart = WaysReadAgain.readAgain(List.of(
                oneOf(1, List.of(List.of(x(1, Rel.LE, 0)), List.of(x(1, Rel.GE, 10))))));

        assertTrue(every.as().orElse(null) instanceof Reachability.Reaching reaching
                        && reaching.ways() instanceof Reachability.Ways.One,
                () -> "left off, the way is not split: " + every.as());
        assertEquals(Optional.empty(), apart.as(), "kept, it is read as it is");
    }

    /**
     * Under {@code ((x <= 0 || x > 0) && t || y >= 10 && u)} the choice inside the first
     * alternative leaves {@code x} every value and comes to nothing, so the first alternative
     * asks nothing of the relation and the choice around it comes to nothing as well, though its
     * alternatives bound two numbers between them.
     */
    @Test
    void aChoiceInsideAnAlternativeComesToNothingWhereItsAlternativesLeaveEveryValue() {
        AWayReadForARelation.ReadAgain again = WaysReadAgain.readAgain(List.of(
                oneOf(1, List.of(
                        List.of(oneOf(2, List.of(List.of(x(1, Rel.LE, 0)),
                                List.of(x(1, Rel.GT, 0)))), truth("t", true)),
                        List.of(WaysReadAgain.y(1, Rel.GE, 10), truth("u", true))))));

        assertTrue(again.as().orElse(null) instanceof Reachability.Reaching reaching
                        && reaching.ways() instanceof Reachability.Ways.One,
                () -> "left off, the way is not split: " + again.as());
    }
}
