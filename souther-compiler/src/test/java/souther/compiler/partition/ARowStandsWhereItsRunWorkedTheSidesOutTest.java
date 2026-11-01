package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.ConditionOutcomeSite;
import souther.compiler.coverage.Numberings;
import souther.compiler.coverage.RecordedVisit;
import souther.compiler.coverage.SeenComparison;
import souther.compiler.coverage.SiteNumbering;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.math.BigInteger;
import java.util.ArrayList;
import souther.compiler.numeric.NumericDomain;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A row stands on a line drawn on how far apart a comparison's sides come out where some visit its
 * run made worked them out that far apart.
 *
 * <p>Read off the run and never worked out again, and taken exactly: two sides each a whole number
 * the language holds stand further apart than it holds, and the comparison answered all the same.
 * A visit the run did not keep is not one that came out elsewhere, and a row whose run was not
 * watched has nothing to read.
 */
class ARowStandsWhereItsRunWorkedTheSidesOutTest {

    private static final SiteNumbering NUMBERING =
            Numberings.of(Numberings.Family.COMPARISON, Numberings.Family.COMPARISON);

    private static final ConditionOutcomeSite SITE = NUMBERING.outcome(0);

    /** A second place the same comparison is recorded at, as a helper called twice writes it. */
    private static final ConditionOutcomeSite OTHER_SITE = NUMBERING.outcome(1);

    private static final BorderQuantity.ComparedOnARun APART = new BorderQuantity.ComparedOnARun(
            "out", new ModelOccurrence(new SourceConstructOrigin(new WrittenOwner.Body("m", "out"),
                    0, 0, SourceConstruct.BINARY), ExpansionLineage.ORIGINAL),
            "misses(xs) - 3", List.of(), List.of(), List.of(), NumericDomain.Bounds.OPEN);

    private static Criterion at(BigInteger level) {
        return new Criterion.AtTheLevel(new Level.OfTheQuantity(ExactRatio.of(level)));
    }

    private static Criterion at(long level) {
        return at(BigInteger.valueOf(level));
    }

    /** A row whose run worked the sides out to each pair in {@code sides}, one visit apiece, and
     *  kept every visit it made. */
    private static BorderQuantity.Observation ran(long[]... sides) {
        return ran(true, sides);
    }

    /** The same, where the recording says whether it kept every visit. */
    private static BorderQuantity.Observation ran(boolean everyVisitKept, long[]... sides) {
        List<SeenComparison> visits = new ArrayList<>();
        for (int nth = 0; nth < sides.length; nth++) {
            visits.add(new SeenComparison(SITE, nth, sides[nth][0], sides[nth][1]));
        }
        return new Unwalked(Optional.of(new BorderQuantity.SidesOnARun(visits, everyVisitKept)));
    }

    /** {@code times} visits, all at {@code left} against three. */
    private static long[][] times(int times, long left) {
        long[][] sides = new long[times][];
        for (int i = 0; i < times; i++) {
            sides[i] = new long[] {left, 3};
        }
        return sides;
    }

    @Test
    void aRowStandsWhereAVisitCameOut() {
        BorderQuantity.Observation row = ran(new long[] {2, 3}, new long[] {3, 3});

        assertEquals(BorderQuantity.Stands.YES, APART.standsAt(at(-1), row));
        assertEquals(BorderQuantity.Stands.YES, APART.standsAt(at(0), row));
        assertEquals(BorderQuantity.Stands.NO, APART.standsAt(at(1), row));
    }

    /** Two whole numbers further apart than one holds are as far apart as they are. */
    @Test
    void howFarApartIsTakenExactly() {
        BorderQuantity.Observation row = ran(new long[] {Long.MIN_VALUE, Long.MAX_VALUE});
        BigInteger apart = BigInteger.valueOf(Long.MIN_VALUE)
                .subtract(BigInteger.valueOf(Long.MAX_VALUE));

        assertEquals(BorderQuantity.Stands.YES, APART.standsAt(at(apart), row));
        assertEquals(BorderQuantity.Stands.NO, APART.standsAt(at(1), row));
    }

    /** A run the recording says went past the visits kept may have come out at the level on one
     *  nobody kept. */
    @Test
    void aRunPastTheVisitsKeptCouldNotBeTold() {
        BorderQuantity.Observation row = ran(false, times(RecordedVisit.MOST, 0));

        assertEquals(BorderQuantity.Stands.YES, APART.standsAt(at(-3), row));
        assertEquals(BorderQuantity.Stands.couldNotTell(ReadingGap.COULD_NOT_READ_ROW),
                APART.standsAt(at(0), row));
    }

    /** As many visits as are kept, every one kept, is a run that stands nowhere else. */
    @Test
    void aRunOfAsManyVisitsAsAreKeptIsReadToTheEnd() {
        BorderQuantity.Observation row = ran(times(RecordedVisit.MOST, 0));

        assertEquals(BorderQuantity.Stands.NO, APART.standsAt(at(0), row));
    }

    /** Places the comparison is recorded at that kept every visit are read to the end, however
     *  many visits they hold between them. */
    @Test
    void visitsOfSeveralPlacesPastTheKeptOfOneAreReadToTheEnd() {
        List<SeenComparison> visits = new ArrayList<>();
        for (ConditionOutcomeSite site : List.of(SITE, OTHER_SITE)) {
            for (int nth = 0; nth < RecordedVisit.MOST - 1; nth++) {
                visits.add(new SeenComparison(site, nth, 0, 3));
            }
        }
        BorderQuantity.Observation row =
                new Unwalked(Optional.of(new BorderQuantity.SidesOnARun(visits, true)));

        assertEquals(BorderQuantity.Stands.NO, APART.standsAt(at(0), row));
    }

    @Test
    void aRowNoRunWasWatchedForCouldNotBeTold() {
        assertEquals(BorderQuantity.Stands.couldNotTell(ReadingGap.COULD_NOT_READ_ROW),
                APART.standsAt(at(0), new Unwalked(Optional.empty())));
    }

    /** A run that never reached the comparison stands at none of its levels. */
    @Test
    void aRunThatNeverComparedStandsNowhere() {
        assertEquals(BorderQuantity.Stands.NO, APART.standsAt(at(0), ran()));
    }

    /** A row read for its run and for no value it wrote. */
    private record Unwalked(Optional<BorderQuantity.SidesOnARun> compared)
            implements BorderQuantity.Observation {

        @Override
        public WalkResult<ObservationAtPoint> at(TermPath path) {
            return WalkResult.couldNotWalk();
        }

        @Override
        public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
            return WalkResult.couldNotWalk();
        }

        @Override
        public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath container) {
            return WalkResult.couldNotWalk();
        }

        @Override
        public Optional<BorderQuantity.SidesOnARun> comparedOnTheRun() {
            return compared;
        }
    }
}
