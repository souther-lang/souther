package souther.compiler.check;

import souther.compiler.numeric.CanonicalOrder;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.ConstantArguments;
import souther.compiler.semantics.ResultRange;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * What a comparison of the number an operation answering the order of its two arguments answered
 * states of those two arguments.
 *
 * <p>What such an operation answers is a sign ({@link #argumentsOf}), so a comparison that settles
 * which side of nought the answer falls on is a comparison of the argument a positive answer names
 * as the greater against the other one. One account for every reader of a condition, so the check
 * and the reading of what a condition means cannot come to read one comparison of a sign as two
 * different orders.
 *
 * <p>Composed in the numeric domain rather than decided here, so that what a step is worth is the
 * step the domain knows about: over whole numbers {@code > -1} is {@code >= 0}, and this would
 * either have to say so a second time or answer as though a sign could fall between the two. The
 * rules taken in are the two there are — what the operation declares of its answer and what the
 * comparison says.
 */
public final class TheSignOfAnOrder {

    private TheSignOfAnOrder() {}

    /** What a comparison of the sign states of the two arguments. */
    public sealed interface Stands {

        /**
         * The argument a positive answer names as the greater stands {@code relation} to the other.
         *
         * @param exactly whether that is all the comparison states, so the two arguments standing
         *                {@code relation} is where it holds and not only something it proves. A
         *                sign held above nought by {@code compare(a, b) > 0} is {@code a > b}; a
         *                count of days held above one by {@code daysBetween(a, b) > 1} proves
         *                {@code b > a} and is not where it holds
         */
        record Between(Rel relation, boolean exactly) implements Stands {

            public Between {
                Objects.requireNonNull(relation, "two arguments stand in some relation");
            }
        }

        /**
         * The same whatever the arguments: every answer the operation can give comes out
         * {@code holds}, so the comparison states no order of them.
         */
        record Settled(boolean holds) implements Stands {}
    }

    /**
     * The two arguments of an operation whose answer is the sign of their order.
     *
     * @param greater the one a positive answer names as the greater
     * @param lesser  the other one
     */
    public record Ordered(DeclaredArgument greater, DeclaredArgument lesser) {

        public Ordered {
            Objects.requireNonNull(greater, "an order has a greater side");
            Objects.requireNonNull(lesser, "and a lesser one");
        }
    }

    /** The two arguments {@code operation} answers the order of, or null where its answer is no
     *  such sign. */
    public static Ordered argumentsOf(ValueName operation) {
        BoundOperationFact.StatesTheOrderOfItsArguments order =
                DefaultBoundOperationFacts.get().statesTheOrderOfItsArguments(operation);
        return order == null ? null : new Ordered(order.greater(), order.lesser());
    }

    /**
     * What the answer of {@code operation}, counted at {@code spacing}, standing {@code rel} to
     * {@code against} states of its two arguments — or null where the two rules leave it open.
     */
    public static Stands of(ValueName operation, Granularity spacing, Rel rel, ExactRatio against) {
        // One atom, standing for the number the operation answered. Nothing else is in this domain:
        // what is asked is what the operation and the comparison prove between them, and a rule
        // about anything else would be a rule about a value that is not the sign.
        Object sign = new Object();
        Map<Object, Granularity> spacings = Map.of(sign, spacing);
        LinearForm<Object> answered = LinearForm.atom(sign);
        // One position, so the order is total on the domain by there being nothing to put in an
        // order. Two of them reaching it would be a second position in a domain written to have
        // one, and it says so rather than choosing between them.
        CanonicalOrder<Object> order = (one, other) -> {
            if (one == other) {
                return 0;
            }
            throw new IllegalStateException("this domain stands for one number and was asked to"
                    + " walk two: " + one + " and " + other);
        };
        NumericDomain<Object> declared = NumericDomain.top(order)
                .assuming(sign, ResultRange.of(DefaultBoundOperationFacts.get()
                        .boundsOnTheResult(operation), ConstantArguments.none()), spacings);
        ExactAnswer<LinearForm<Object>> compared = answered.minus(LinearForm.constant(against));
        if (!(compared instanceof ExactAnswer.Held<LinearForm<Object>>(LinearForm<Object> form))) {
            return null;
        }
        NumericDomain<Object> known = declared.assume(form, rel, spacings);
        if (known.isBottom()) {
            return new Stands.Settled(false);
        }
        // Asked of each side of nought apart: the answers below it, at it and above it. Where the
        // comparison holds on every answer of a side or on none, what it states is which sides it
        // holds on, and that is a relation of the arguments exactly. Asked of the whole at once, a
        // sign held away from nought is two intervals the domain holds as one, and `!= 0` would
        // prove nothing about the order it is.
        List<Rel> holds = new ArrayList<>();
        boolean failsSomewhere = false;
        boolean decided = true;
        for (Rel side : List.of(Rel.LT, Rel.EQ, Rel.GT)) {
            NumericDomain<Object> there = declared.assume(answered, side, spacings);
            if (there.isBottom()) {
                continue;
            }
            if (there.entails(form, rel)) {
                holds.add(side);
            } else if (there.assume(form, rel, spacings).isBottom()) {
                failsSomewhere = true;
            } else {
                decided = false;
            }
        }
        if (decided && !failsSomewhere) {
            return new Stands.Settled(true);
        }
        // Tightest first: a sign held at nought is an equality and not two half-statements, and one
        // held above it says more than one held at or above it. The first that covers every side
        // the comparison holds on is those sides and no other, since each one side and each two
        // of them is one of these, so it covers none it fails on.
        for (Rel each : List.of(Rel.EQ, Rel.GT, Rel.LT, Rel.GE, Rel.LE, Rel.NE)) {
            if (decided && holds.stream().allMatch(side -> covers(each, side))) {
                return new Stands.Between(each, true);
            }
        }
        // A side the comparison holds on only some of: what it proves of the order is all that is
        // left to say, and that is not where it holds.
        for (Rel each : List.of(Rel.EQ, Rel.GT, Rel.LT, Rel.GE, Rel.LE, Rel.NE)) {
            if (known.entails(answered, each)) {
                return new Stands.Between(each, false);
            }
        }
        return null;
    }

    /** Whether the answers on {@code side} of nought — below, at or above it — all stand
     *  {@code relation} to it. */
    private static boolean covers(Rel relation, Rel side) {
        return relation.holds(switch (side) {
            case LT -> -1;
            case EQ -> 0;
            case GT -> 1;
            default -> throw new IllegalArgumentException("a side of nought is below, at or above"
                    + " it: " + side);
        });
    }
}
