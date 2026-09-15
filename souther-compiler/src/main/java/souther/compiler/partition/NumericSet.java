package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Place;

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.ArrayList;
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

        /**
         * The one number there is, where the window holds it.
         *
         * <p>Walked for, this would step from the bottom of the window to reach a number it already
         * has. And it is offered whole or not: a set of one number is that number, and whether an
         * account can build at a number of that shape is the account's answer rather than a reason
         * to withhold it — a total of a half is a total something adds up to.
         */
        @Override
        public List<Place> within(Carrier carrier, BigDecimal from, BigDecimal to, int many) {
            return many > 0 && value instanceof Count count
                    && count.at().compareTo(from) >= 0 && count.at().compareTo(to) <= 0
                    ? List.of(value) : List.of();
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
    }

    /** Inside one of the runs the lines a rule drew cut the position into. */
    record InARun(Band run) implements NumericSet {

        @Override
        public boolean holds(Place at, Carrier carrier) {
            return run.holds(new Level.OnACarrier(carrier, at));
        }

        /**
         * The same, begun at the run's own lower end rather than at the bottom of the window.
         *
         * <p>What the window says a number of this kind can be at all is the account's, and it is as
         * wide as the kind allows — the years a date can fall in, every count a container might
         * hold. Stepped through from there, a run that starts high is reached one number at a time,
         * and what is a choice between a few candidates becomes a walk over the whole kind.
         */
        @Override
        public List<Place> within(Carrier carrier, BigDecimal from, BigDecimal to, int many) {
            return whole(this, carrier, start(from), stop(to), many);
        }

        /** The first whole number the run holds, or the window's own start where the run runs
         *  past it. */
        private BigDecimal start(BigDecimal from) {
            Endpoint below = run.lineBelow(null);
            if (below == null || !(below.at() instanceof Count count)) {
                return from;
            }
            // The line itself where the run keeps it, and the one above where it does not.
            BigDecimal edge = count.at().setScale(0, RoundingMode.CEILING);
            return from.max(!below.inclusive() && edge.compareTo(count.at()) == 0
                    ? edge.add(BigDecimal.ONE) : edge);
        }

        /**
         * The last whole number the run holds, or the window's own end where the run runs past it.
         *
         * <p>Both ends and not only the near one. A run that ends below where the window starts
         * holds nothing the window can offer, and a walk that only knew where to begin would step
         * through the whole window to find that out.
         */
        private BigDecimal stop(BigDecimal to) {
            Endpoint above = run.lineAbove(null);
            if (above == null || !(above.at() instanceof Count count)) {
                return to;
            }
            BigDecimal edge = count.at().setScale(0, RoundingMode.FLOOR);
            return to.min(!above.inclusive() && edge.compareTo(count.at()) == 0
                    ? edge.subtract(BigDecimal.ONE) : edge);
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
     * Whole numbers of this set from {@code from} to {@code to}, smallest first, at most
     * {@code many} of them.
     *
     * <p><b>Candidates, and not the whole of what is here.</b> A caller that tried all of these and
     * built nothing has shown the set empty only where the list is short of what it asked for;
     * where the list is full, what stopped the search is the caller's own number. The two are told
     * apart by the size of what comes back, and every caller that reports why it found nothing
     * reads that difference.
     *
     * <p>Whole numbers, because the callers are the accounts whose numbers are whole: how many a
     * container holds, a part of a time or a date, a quotient. What stands at a position is not one
     * of those, and the place for it is chosen against the carrier by the reader that holds the
     * order's own ends.
     *
     * <p>The window is the caller's and not the set's. What a number of this kind can be at all is
     * the account's own — a month runs to twelve however far the rules leave the number — so the
     * account hands the window in and this narrows it to the numbers the rules admit.
     */
    default List<Place> within(Carrier carrier, BigDecimal from, BigDecimal to, int many) {
        return whole(this, carrier, from, to, many);
    }

    /**
     * Whether {@code tried} is every number of this set the window it was taken from holds.
     *
     * <p>What tells a search that found nothing from a search that proved there is nothing. A list
     * short of what the caller asked for ran out of numbers rather than out of room, so it is
     * everything the window held; a full one stopped because the caller said how many to take.
     */
    default boolean allOfThem(List<Place> tried, int many) {
        return tried.size() < many;
    }

    private static List<Place> whole(NumericSet set, Carrier carrier, BigDecimal from,
                                     BigDecimal to, int many) {
        List<Place> out = new ArrayList<>();
        for (BigDecimal at = from; at.compareTo(to) <= 0 && out.size() < many;
                at = at.add(BigDecimal.ONE)) {
            Count place = new Count(at);
            if (set.holds(place, carrier)) {
                out.add(place);
            }
        }
        return List.copyOf(out);
    }
}
