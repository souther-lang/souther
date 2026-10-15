package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.ReadingsOfEachValue;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.numeric.Congruences;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.Place;
import souther.compiler.values.ValueSet;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;

/**
 * What a position's declarations hold its value to besides where it runs: the class of whole
 * numbers it is of and the values they name — and whether a value or a run of the position's order
 * is one they refuse. And what they hold a number taken of the value to: the numbers the values
 * they name come to. And a form over numbers of that one position: what the form comes to of each
 * value they name.
 *
 * <p>The one place that question is answered. Whether a line is drawn at a value, whether a run
 * between lines is a class, and whether a border owes a row at a point or in a run each ask it, and
 * each has to come to the same answer of the same facts: a reader asking some of them alone would
 * draw a line at {@code "a0"} on a position held to {@code "a"} or {@code "b"}, keep a class
 * nothing can stand in, or owe a row at a value the declarations refuse, while the others did not.
 *
 * <p>Neither is where the value runs. A range is convex and the order's own reading already holds
 * it; what is here is what a range cannot say — the values between its ends that are not values of
 * the position.
 *
 * <p>Only ever a refusal. The values named are what the rules that were read name, so a value they
 * name is not shown to be one a row can hold, and nothing here says that a run holds something.
 *
 * <p>Which of these a quantity is held to is the quantity's own answer
 * ({@link BorderQuantity#heldIn}).
 */
public sealed interface HeldValues {

    /** Nothing held: a quantity read of no one position, or one whose rules say neither. */
    HeldValues NONE = OfAPosition.NONE;

    /** Whether the declarations refuse {@code level}. */
    boolean refuses(Level level);

    /**
     * Whether the declarations leave nothing in {@code part} of where the value runs, so far as
     * that is said without building anything.
     *
     * @param within where the value runs, or null where nothing bounds it
     */
    boolean leaveNothingIn(LevelInterval part, NumericDomain.Bounds within);

    /**
     * What the declarations {@code region} reads hold the number {@code orders} is of to, on the
     * order it is answered on.
     *
     * <p>A number taken of a position is held to the numbers the values its rules name come to
     * ({@link SearchRegion#heldAt}): a string held to {@code "a"} or {@code "b"} is held to a
     * length of one. The class is the value's own, so it is said of the value and of nothing taken
     * of it.
     */
    static OfAPosition of(SearchRegion region, TermOrders orders) {
        NumericTerm.FromOnePosition one = orders.term().atOnePosition();
        if (one == null) {
            return OfAPosition.NONE;
        }
        OfAPosition held = new OfAPosition(orders.answered(),
                one instanceof NumericTerm.ValueOf value ? region.valueClassAt(value) : null,
                region.heldAt(one));
        return held.holdsAnything() ? held : OfAPosition.NONE;
    }

    /**
     * What the declarations hold a number of one position to.
     *
     * <p>Made where the declarations were read ({@link #of(SearchRegion, TermOrders)}), and in this
     * package by a test that wants a synthetic one. A set named here is what a refusal is concluded
     * from, so it is not one a reader elsewhere can write down.
     */
    final class OfAPosition implements HeldValues {

        static final OfAPosition NONE = new OfAPosition(null, null, ValueSet.ANY);

        private final Carrier on;
        private final Congruences class_;
        private final ValueSet named;

        /**
         * @param on the order the number is answered on, or null where it is read of no one
         *           position's value and nothing here applies
         * @param class_ the class of whole numbers every value is of, or null where none is known
         * @param named the values the position's rules admit, or the numbers those come to where
         *              the number is taken of the position's value
         */
        OfAPosition(Carrier on, Congruences class_, ValueSet named) {
            this.on = on;
            this.class_ = class_;
            this.named = named;
        }

        /** The values the position's rules admit, or the numbers those come to. */
        ValueSet named() {
            return named;
        }

        /**
         * Whether the declarations refuse {@code level}.
         *
         * <p>The class is asked of the number a level is, as a range is; the values named are asked
         * only of a level on the order the number is answered on, since put to a level of another
         * order a set says it holds no such value — which reads as a refusal nobody made.
         */
        @Override
        public boolean refuses(Level level) {
            if (on == null) {
                return false;
            }
            if (level instanceof Level.OnACarrier at && at.of().equals(on)
                    && !on.admitted(named, at.at())) {
                return true;
            }
            ExactRatio number = level.asANumber();
            return class_ != null && number != null && number.isWhole()
                    && number.floor() instanceof ExactAnswer.Held<BigInteger> whole
                    && !whole.value().mod(class_.modulus()).equals(class_.residue());
        }

        /**
         * Whether the declarations leave nothing in {@code part} of where the value runs.
         *
         * <p>Asked of the part inside {@code within} and not of the part alone. A run reaching past
         * an end of the range holds values the declarations never leave, and a set named by the
         * values it keeps away from is shown to leave a run nothing only where the run has ends to
         * count between.
         *
         * <p>Not of a run with an end that is no place of the position — one in a written form's
         * units — which neither says anything of. The class is asked only of the whole numbers,
         * which are what a class is of.
         */
        @Override
        public boolean leaveNothingIn(LevelInterval part, NumericDomain.Bounds within) {
            if (on == null) {
                return false;
            }
            OrderedInterval asked = LevelRealizer.runOf(part, on);
            if (asked == null) {
                return false;
            }
            OrderedInterval run = within == null ? asked
                    : asked.meet(new OrderedInterval(within.min(), within.max()));
            if (on.admitsNothingIn(named, run)) {
                return true;
            }
            return class_ != null && on instanceof Carrier.Whole
                    && ClassMembers.within(class_, new NumericDomain.Bounds(run.low(), run.high()),
                            null, 1).values().isEmpty();
        }

        private boolean holdsAnything() {
            return class_ != null || !named.isAny();
        }
    }

    /**
     * What a form over numbers of one position comes to of the values that position's rules name.
     *
     * <p>Each value read through every term of the form together, and the form worked out of what
     * that one value reads as ({@link SearchRegion#readingsOfEach}). Of {@code 4}, {@code 8} and
     * {@code 10}, {@code c - Int.floorMod(c, 3)} comes to three, six and nine: the numbers each term
     * comes to on its own are {@code {4, 8, 10}} and {@code {1, 2}}, and put together apart from the
     * values they were read of they would reach five, which no value does.
     *
     * <p>A distance between two such numbers is the form that is their difference, and a remainder
     * of such a form is what the form leaves by its divisor: the levels are what those come to.
     *
     * <p>Made only of every value the position admits ({@link #of}): a level none of them comes to
     * is refused, so a list missing one would refuse a level a value reaches.
     */
    final class OfAForm implements HeldValues {

        /** What the form comes to of each value the position admits. */
        private final List<ExactRatio> comesTo;

        private OfAForm(List<ExactRatio> comesTo) {
            this.comesTo = List.copyOf(comesTo);
        }

        /**
         * What a quantity over {@code terms} comes to of each value their one position admits, or
         * nothing where the terms are not all of one position, where the position admits no
         * finite set, or where what one value comes to is not worked out.
         *
         * @param comesTo the level the quantity is at where its terms read as given, or none where
         *                it is at no level there — a remainder of a form that comes to no whole
         *                number
         */
        static HeldValues of(SearchRegion region, List<NumericTerm> terms,
                             Function<Map<NumericTerm, Place>, ExactAnswer<Optional<ExactRatio>>>
                                     comesTo) {
            List<NumericTerm.FromOnePosition> named = new ArrayList<>();
            for (NumericTerm each : terms) {
                if (each.atOnePosition() == null) {
                    return NONE;
                }
                named.add(each.atOnePosition());
            }
            ReadingsOfEachValue read = region.readingsOfEach(named);
            if (read == null) {
                return NONE;
            }
            List<ExactRatio> out = new ArrayList<>();
            for (ReadingsOfEachValue.Read each : read.each()) {
                if (!(comesTo.apply(each.numbers())
                        instanceof ExactAnswer.Held<Optional<ExactRatio>>(var at))) {
                    return NONE;
                }
                at.ifPresent(out::add);
            }
            return new OfAForm(out);
        }

        /** Whether no value comes to {@code level}, of a level of the form. */
        @Override
        public boolean refuses(Level level) {
            return level instanceof Level.OfTheQuantity(ExactRatio at)
                    && comesTo.stream().noneMatch(each -> each.compareTo(at) == 0);
        }

        /** Whether no value comes to anything in {@code part}. What the form runs between says
         *  nothing a value does not already. */
        @Override
        public boolean leaveNothingIn(LevelInterval part, NumericDomain.Bounds within) {
            return comesTo.stream().noneMatch(each -> part.contains(new Level.OfTheQuantity(each)));
        }
    }
}
