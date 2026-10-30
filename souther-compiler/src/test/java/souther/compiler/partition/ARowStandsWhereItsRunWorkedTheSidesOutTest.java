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

    private static final SiteNumbering NUMBERING = Numberings.of(Numberings.Family.COMPARISON);

    private static final ConditionOutcomeSite SITE = NUMBERING.outcome(0);

    private static final BorderQuantity.ComparedOnARun APART = new BorderQuantity.ComparedOnARun(
            "out", new ModelOccurrence(new SourceConstructOrigin(new WrittenOwner.Body("m", "out"),
                    0, 0, SourceConstruct.BINARY), ExpansionLineage.ORIGINAL),
            "misses(xs) - 3", List.of(), List.of(), List.of());

    private static Criterion at(BigInteger level) {
        return new Criterion.AtTheLevel(new Level.OfTheQuantity(ExactRatio.of(level)));
    }

    private static Criterion at(long level) {
        return at(BigInteger.valueOf(level));
    }

    /** A row whose run worked the sides out to each pair in {@code sides}, one visit apiece. */
    private static BorderQuantity.Observation ran(long[]... sides) {
        List<SeenComparison> visits = new ArrayList<>();
        for (int nth = 0; nth < sides.length; nth++) {
            visits.add(new SeenComparison(SITE, nth, sides[nth][0], sides[nth][1]));
        }
        return new Unwalked(Optional.of(visits));
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

    /** A run past the visits kept may have come out at the level on one nobody kept. */
    @Test
    void aRunPastTheVisitsKeptCouldNotBeTold() {
        long[][] sides = new long[RecordedVisit.MOST][];
        for (int i = 0; i < sides.length; i++) {
            sides[i] = new long[] {0, 3};
        }
        BorderQuantity.Observation row = ran(sides);

        assertEquals(BorderQuantity.Stands.YES, APART.standsAt(at(-3), row));
        assertEquals(BorderQuantity.Stands.couldNotTell(ReadingGap.COULD_NOT_READ_ROW),
                APART.standsAt(at(0), row));
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
    private record Unwalked(Optional<List<SeenComparison>> compared)
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
        public Optional<List<SeenComparison>> comparedOnTheRun() {
            return compared;
        }
    }
}
