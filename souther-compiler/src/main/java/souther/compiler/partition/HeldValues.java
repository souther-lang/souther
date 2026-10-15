package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.numeric.Congruences;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.values.ValueSet;

import java.math.BigInteger;

/**
 * What a position's declarations hold its value to besides where it runs: the class of whole
 * numbers it is of and the values they name — and whether a value or a run of the position's order
 * is one they refuse. And what they hold a number taken of the value to: the numbers the values
 * they name come to.
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
 * @param on the order the number is answered on, or null where it is read of no one position's
 *           value and nothing here applies
 * @param class_ the class of whole numbers every value is of, or null where none is known
 * @param named the values the position's rules admit, or the numbers those come to where the
 *              number is taken of the position's value
 */
record HeldValues(Carrier on, Congruences class_, ValueSet named) {

    /** Nothing held: a quantity read of no one position, or one whose rules say neither. */
    static final HeldValues NONE = new HeldValues(null, null, ValueSet.ANY);

    /**
     * What the declarations {@code region} reads hold the number {@code orders} is of to, on the
     * order it is answered on.
     *
     * <p>A number taken of a position is held to the numbers the values its rules name come to
     * ({@link TermOrders#readOfEach}): a string held to {@code "a"} or {@code "b"} is held to a
     * length of one. The class is the value's own, so it is said of the value and of nothing taken
     * of it.
     */
    static HeldValues of(SearchRegion region, TermOrders orders) {
        NumericTerm.FromOnePosition one = orders.term().atOnePosition();
        if (one == null) {
            return NONE;
        }
        HeldValues held = one instanceof NumericTerm.ValueOf value
                ? new HeldValues(orders.answered(), region.valueClassAt(value),
                        region.admittedAt(value))
                : new HeldValues(orders.answered(), null, orders.readOfEach(
                        region.admittedAt(new NumericTerm.ValueOf(one.position()))));
        return held.holdsAnything() ? held : NONE;
    }

    /**
     * Whether the declarations refuse {@code level}.
     *
     * <p>The class is asked of the number a level is, as a range is; the values named are asked
     * only of a level on the order the number is answered on, since put to a level of another
     * order a set says it holds no such value — which reads as a refusal nobody made.
     */
    boolean refuses(Level level) {
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
     * Whether the declarations leave nothing in {@code part} of where the value runs, so far as
     * that is said without building anything.
     *
     * <p>Asked of the part inside {@code within} and not of the part alone. A run reaching past an
     * end of the range holds values the declarations never leave, and a set named by the values it
     * keeps away from is shown to leave a run nothing only where the run has ends to count between.
     *
     * <p>Not of a run with an end that is no place of the position — one in a written form's
     * units — which neither says anything of. The class is asked only of the whole numbers, which
     * are what a class is of.
     *
     * @param within where the value runs, or null where nothing bounds it
     */
    boolean leaveNothingIn(LevelInterval part, NumericDomain.Bounds within) {
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
