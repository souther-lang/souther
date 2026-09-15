package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;

import java.util.List;

/**
 * The numbers a question is about, as the set of them.
 *
 * <p><b>One vocabulary read in both directions.</b> A class of a number is about these numbers and
 * answers whether a row's number is one of them; a search for a value to write is asked for a value
 * whose number is one of them. Those are the two directions of one fact, and they are said here
 * once — so a reader that has a row and a reader that has to compose one cannot come to disagree
 * about which numbers were meant.
 *
 * <p><b>A set and not a chosen member of it.</b> Which of these a value is written at is a choice
 * about the value ({@link TermRealizations}), and it is made where the value is made. Projected to
 * one member before the question is asked, the answer about that member is all there is, and a
 * reader that took it for an answer about the set would say nothing writes a value in a range
 * because nothing writes one at the place it happened to pick.
 *
 * <p><b>Membership, and nothing about how to walk to a member.</b> Which numbers to try, how they
 * step and how far they run are three answers this does not have. How the values of a number step
 * is the carrier's — whole for a count, dense for a decimal or a moment — and how far they run is
 * the account's, since a part of a time stops where the part does and a whole number stops where
 * the carrier does. Answered here, one walk would stand for every account: a run between a tenth
 * and nine tenths would hold nothing because no whole number is in it, and a quotient past what an
 * int holds would be a number nothing offers.
 *
 * <p>Closed, with an arm per shape the rules leave. A rule that singles a value out leaves that
 * value and everything else; a rule that draws a line leaves the runs between the lines. A shape
 * added is an arm here, and everything that reads one of these stops compiling until it says what
 * it does about the new shape.
 */
public sealed interface NumericSet {

    /** Exactly the value a rule singled out. */
    record At(Place value) implements NumericSet {

        @Override
        public boolean holds(Place at, Carrier carrier) {
            return at.sameAs(value);
        }

        @Override
        public NumericDomain.Bounds extent() {
            return new NumericDomain.Bounds(new Endpoint(value, true), new Endpoint(value, true));
        }
    }

    /**
     * None of the values any rule singled out, which is the set those leave behind.
     *
     * <p>Held as what it excludes rather than as the runs between them. The values a rule singles
     * out need not be on an order that has runs at all, and what this says — anything but these —
     * is what a search for a value is asked and is what a row is read against.
     */
    record AwayFrom(List<Place> values) implements NumericSet {

        public AwayFrom {
            values = List.copyOf(values);
        }

        @Override
        public boolean holds(Place at, Carrier carrier) {
            return values.stream().noneMatch(at::sameAs);
        }

        /** As far as the order runs, either way: what a rule holds a number away from leaves every
         *  number but those, and they are holes rather than ends. */
        @Override
        public NumericDomain.Bounds extent() {
            return new NumericDomain.Bounds(null, null);
        }
    }

    /** Inside one of the runs the lines a rule drew cut the position into. */
    record InARun(Band run) implements NumericSet {

        @Override
        public boolean holds(Place at, Carrier carrier) {
            return run.holds(new Level.OnACarrier(carrier, at));
        }

        @Override
        public NumericDomain.Bounds extent() {
            return new NumericDomain.Bounds(run.lineBelow(null), run.lineAbove(null));
        }
    }

    /**
     * Whether {@code at} is one of these numbers, on the order they are counted on.
     *
     * <p>The set's own answer, because the set is what knows. Asked by a reader walking the shapes
     * itself, the walk would be a second place the shapes are enumerated, and a shape added is
     * exactly where a second walk is not.
     */
    boolean holds(Place at, Carrier carrier);

    /**
     * The ends outside which this holds nothing, open at either end where it runs as far as the
     * order does.
     *
     * <p>Where this set lies, which is a fact about the set and the other half of what membership
     * says. Not how to walk to a member of it: how the numbers step and how many of them are worth
     * trying stay with the account, and this only keeps that walk from starting where there is
     * nothing — a year at or after two thousand is eight numbers to try and a billion to step over
     * to reach them.
     *
     * <p>Asked rather than worked out by a reader looking at which shape it holds, for the reason
     * membership is: a shape added is answered here, not in however many walks had a condition on
     * the shapes they knew.
     */
    NumericDomain.Bounds extent();
}
