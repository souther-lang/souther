package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The theorem, asked with nothing of either reader in the question.
 *
 * <p>Two readers project onto {@link Induction}: the one that discharges a rule about a construction
 * and the one that measures where a model divides. What is checked here is neither of them — a seed,
 * a step and what the step is handed, put through the proof and read back as the range it settles.
 *
 * <p>Both steps the language accumulates by are here, and the one it has no number for. Which of
 * them a reader has arithmetic for is that reader's own answer; that the proof carries all of them
 * is what lets a reader gain one without a line being written in the proof.
 */
class AWalkIsProvedToStayInARangeWithoutAnybodysVocabularyTest {

    private enum Atom {
        ACCUMULATOR,
        ELEMENT
    }

    /** Both numbers are whole ones, which a range asserted about either of them is held to. */
    private static final Map<Atom, Granularity> WHOLE_NUMBERS =
            Map.of(Atom.ACCUMULATOR, Granularity.DISCRETE, Atom.ELEMENT, Granularity.DISCRETE);

    private static final LinearForm<Atom> ACCUMULATOR =
            LinearForm.atom(Atom.ACCUMULATOR);

    private static final LinearForm<Atom> ADDED =
            ACCUMULATOR.plus(LinearForm.atom(Atom.ELEMENT));

    /** A walk whose step adds, read against a domain holding the two numbers. */
    private record Adding(NumericDomain<Atom> reading, NumericDomain.Bounds element,
                          NumericDomain.Bounds seed) implements Induction.Prepared {

        @Override
        public boolean isBottom() {
            return reading.isBottom();
        }

        @Override
        public NumericDomain.Bounds seed() {
            return seed;
        }

        @Override
        public NumericDomain.Bounds step() {
            return reading.boundsOf(ADDED);
        }

        @Override
        public Collection<NumericDomain.Bounds> whatTheStepIsHanded() {
            return List.of(element);
        }

        @Override
        public Induction.Prepared assuming(NumericDomain.Bounds candidate) {
            return new Adding(reading.assuming(Atom.ACCUMULATOR, candidate, WHOLE_NUMBERS), element, seed);
        }
    }

    /** The same with a step that multiplies, which is not a form and is the interval algebra's. */
    private record Multiplying(NumericDomain<Atom> reading, NumericDomain.Bounds element,
                               NumericDomain.Bounds seed) implements Induction.Prepared {

        @Override
        public boolean isBottom() {
            return reading.isBottom();
        }

        @Override
        public NumericDomain.Bounds seed() {
            return seed;
        }

        @Override
        public NumericDomain.Bounds step() {
            return Intervals.product(reading.boundsOf(ACCUMULATOR), element);
        }

        @Override
        public Collection<NumericDomain.Bounds> whatTheStepIsHanded() {
            return List.of(element);
        }

        @Override
        public Induction.Prepared assuming(NumericDomain.Bounds candidate) {
            return new Multiplying(reading.assuming(Atom.ACCUMULATOR, candidate, WHOLE_NUMBERS), element,
                    seed);
        }
    }

    /** A walk that starts at nought and adds every value it is handed. */
    private static String addingFrom(long seed, NumericDomain.Bounds element) {
        return show(Induction.proves(element, walked ->
                new Adding(NumericDomain.<Atom>top().assuming(Atom.ELEMENT, walked, WHOLE_NUMBERS),
                        walked, at(seed))));
    }

    /** And one that starts at one and multiplies. */
    private static String multiplyingFrom(long seed, NumericDomain.Bounds element) {
        return show(Induction.proves(element, walked ->
                new Multiplying(NumericDomain.<Atom>top().assuming(Atom.ELEMENT, walked, WHOLE_NUMBERS),
                        walked, at(seed))));
    }

    /** A total of values at or above nought is at or above nought, and nothing bounds it above. */
    @Test
    void aSumOfValuesAtOrAboveNoughtStaysThere() {
        assertEquals("0 to unbounded", addingFrom(0, from(0)));
    }

    /**
     * And a total of values at or above five is still only at or above nought.
     *
     * <p>The container may hold none of them, and then the walk answers its seed. Nothing here reads
     * how many it holds, so the seed is what keeps the floor where it is.
     */
    @Test
    void aSumOfValuesFurtherUpIsStillOnlyAboveItsSeed() {
        assertEquals("0 to unbounded", addingFrom(0, from(5)));
    }

    /** A product of values at or above one, started at one, stays at or above one. */
    @Test
    void aProductOfValuesAtOrAboveOneStaysThere() {
        assertEquals("1 to unbounded", multiplyingFrom(1, from(1)));
    }

    /** Values that may be below nought bound a total at neither end, whichever step is repeated. */
    @Test
    void valuesCrossingNoughtProveNothing() {
        assertEquals("unbounded to unbounded", addingFrom(0, between(-3, 3)));
        assertEquals("unbounded to unbounded", multiplyingFrom(1, between(-3, 3)));
    }

    /** And values nothing bounds bound nothing. */
    @Test
    void valuesNothingBoundsProveNothing() {
        assertEquals("unbounded to unbounded",
                addingFrom(0, new NumericDomain.Bounds(null, null)));
    }

    private static NumericDomain.Bounds at(long value) {
        Endpoint end = Endpoint.inclusive(Count.of(BigDecimal.valueOf(value)));
        return new NumericDomain.Bounds(end, end);
    }

    private static NumericDomain.Bounds from(long least) {
        return new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(BigDecimal.valueOf(least))), null);
    }

    private static NumericDomain.Bounds between(long least, long most) {
        return new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(BigDecimal.valueOf(least))),
                Endpoint.inclusive(Count.of(BigDecimal.valueOf(most))));
    }

    private static String show(NumericDomain.Bounds bounds) {
        return (bounds.min() == null ? "unbounded" : bounds.min().at())
                + " to " + (bounds.max() == null ? "unbounded" : bounds.max().at());
    }
}
