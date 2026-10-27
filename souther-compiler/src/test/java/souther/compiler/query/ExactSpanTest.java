package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which axes of the space the rows span the rows reach, which is what says whether the weights of
 * the positions are fixed by them.
 */
class ExactSpanTest {

    private static ExactRatio[] vector(long... places) {
        ExactRatio[] out = new ExactRatio[places.length];
        for (int at = 0; at < places.length; at++) {
            out[at] = ExactRatio.of(places[at]);
        }
        return out;
    }

    @Test
    void aRowThatMovesOnePositionAloneReachesThatAxisAndNoOther() {
        ExactSpan span = new ExactSpan(3);
        span.add(vector(100, 0, 0));
        assertTrue(span.reaches(0));
        assertFalse(span.reaches(1));
        assertFalse(span.reaches(2));
    }

    /** Three rows that each move two of three positions fix all three, though no row moves one
     *  alone. */
    @Test
    void rowsThatEachMoveSeveralPositionsCanReachEveryAxis() {
        ExactSpan span = new ExactSpan(3);
        span.add(vector(1, 1, 0));
        span.add(vector(1, 0, 1));
        assertFalse(span.reaches(0), "two of the three are not enough");
        span.add(vector(0, 1, 1));
        assertTrue(span.reaches(0));
        assertTrue(span.reaches(1));
        assertTrue(span.reaches(2));
    }

    /** A row that is a multiple of one already taken adds nothing. */
    @Test
    void aRowDependentOnTheOthersReachesNothingNew() {
        ExactSpan span = new ExactSpan(2);
        span.add(vector(1, 1));
        span.add(vector(2, 2));
        assertFalse(span.reaches(0));
        assertFalse(span.reaches(1));
    }

    /** Two rows that span a plane reach the axes in it and not the ones that only a row out of it
     *  reaches. */
    @Test
    void aPlaneReachesOnlyTheAxesInIt() {
        ExactSpan span = new ExactSpan(3);
        span.add(vector(1, 0, 1));
        span.add(vector(0, 1, 1));
        assertFalse(span.reaches(0));
        assertFalse(span.reaches(1));
        assertFalse(span.reaches(2));
        span.add(vector(0, 0, 1));
        assertTrue(span.reaches(0));
        assertTrue(span.reaches(1));
        assertTrue(span.reaches(2));
    }

    /** A position weighed against the others: rows (100, 0) and (120, -20) fix both weights. */
    @Test
    void aWeightOfMinusOneIsFixedByRowsThatMoveBothPositions() {
        ExactSpan span = new ExactSpan(2);
        span.add(vector(100, 0));
        span.add(vector(120, -20));
        assertTrue(span.reaches(0));
        assertTrue(span.reaches(1));
    }

    /** The order the rows come in decides nothing. */
    @Test
    void theOrderOfTheRowsDecidesNothing() {
        ExactSpan one = new ExactSpan(3);
        one.add(vector(1, 1, 0));
        one.add(vector(1, 0, 1));
        one.add(vector(0, 1, 1));
        ExactSpan other = new ExactSpan(3);
        other.add(vector(0, 1, 1));
        other.add(vector(1, 1, 0));
        other.add(vector(1, 0, 1));
        for (int at = 0; at < 3; at++) {
            assertTrue(one.reaches(at) == other.reaches(at), "axis " + at);
        }
    }
}
