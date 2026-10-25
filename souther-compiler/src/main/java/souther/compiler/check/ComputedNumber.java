package souther.compiler.check;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.BinOp;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * A number a clause writes as exact arithmetic over places: sums, differences and products, what
 * the library says an operation answers as a form of its arguments, and a rounding to a step.
 *
 * <p>What a place comes to decides what this comes to, and nothing else does: with every place at
 * one number the arithmetic answers one number, exactly, the way the run time answers it. With
 * every place somewhere in a range it answers a range that holds every number it can come to. That
 * is all this reads. It states no relation of the number to a place, because the interval algebra
 * has atoms for a number and rules between atoms, and a number made of places is one more atom
 * whose rule to them is this.
 *
 * <p>What an operation means is the library's to say ({@link BoundOperationFacts}) and is asked of
 * it: this composes the expression and defines no operation of its own. Only what is written wholly
 * of those. A call the library states neither of, a quotient, a choice or a place that is not a
 * place of the value leaves the number unread, and the clause is not taken in through it.
 */
final class ComputedNumber {

    /** What is computed: a place, a written number, or an operation over those. */
    private sealed interface Expr {

        record Place(Term term) implements Expr {}

        record Written(ExactRatio number) implements Expr {}

        /** Each step keeps the term it was read from, whose value is of a type of its own: what a
         *  step answers is counted on the order of that type, and never on the order of what it
         *  was made of. */
        record Negated(Term term, Expr operand) implements Expr {}

        record Operated(Term term, BinOp operator, Expr left, Expr right) implements Expr {}

        /** A constant and each argument at its weight, as the library states an answer. */
        record Weighed(Term term, ExactRatio constant, List<Weight> weights) implements Expr {}

        record Rounded(Term term, BigInteger scale, WholeRounding way, Expr inner)
                implements Expr {}
    }

    private record Weight(ExactRatio coefficient, Expr argument) {}

    /**
     * Where a number lies: both ends included, and an end that is null is not bounded.
     *
     * <p>Closed however the places' own ends are, which makes it hold at least every number the
     * arithmetic can come to.
     */
    record Range(ExactRatio low, ExactRatio high) {

        static final Range ANY = new Range(null, null);

        static Range at(ExactRatio number) {
            return new Range(number, number);
        }

        Range plus(Range other) {
            return new Range(sum(low, other.low), sum(high, other.high));
        }

        Range negated() {
            return new Range(high == null ? null : high.negated(),
                    low == null ? null : low.negated());
        }

        Range times(Range other) {
            End[] ends = {
                End.of(low, -1).times(End.of(other.low, -1)),
                End.of(low, -1).times(End.of(other.high, 1)),
                End.of(high, 1).times(End.of(other.low, -1)),
                End.of(high, 1).times(End.of(other.high, 1))};
            End least = ends[0];
            End most = ends[0];
            for (End each : ends) {
                least = each.compareTo(least) < 0 ? each : least;
                most = each.compareTo(most) > 0 ? each : most;
            }
            return new Range(least.finite(), most.finite());
        }

        private static ExactRatio sum(ExactRatio one, ExactRatio other) {
            return one == null || other == null ? null : one.plus(other).orNull();
        }
    }

    /** One end of a range, which may be past every number. */
    private record End(int beyond, ExactRatio at) implements Comparable<End> {

        /** The end {@code number} is, or the one past every number on the side {@code side}
         *  where there is none. */
        static End of(ExactRatio number, int side) {
            return number == null ? new End(side, null) : new End(0, number);
        }

        ExactRatio finite() {
            return beyond == 0 ? at : null;
        }

        End times(End other) {
            if (beyond == 0 && other.beyond == 0) {
                ExactRatio product = at.times(other.at).orNull();
                // A product the host cannot hold lies somewhere past every number it can.
                return product == null ? new End(at.signum() * other.at.signum() >= 0 ? 1 : -1,
                        null) : new End(0, product);
            }
            if ((beyond == 0 && at.isZero()) || (other.beyond == 0 && other.at.isZero())) {
                return new End(0, ExactRatio.ZERO);
            }
            int one = beyond != 0 ? beyond : at.signum();
            int another = other.beyond != 0 ? other.beyond : other.at.signum();
            return new End(one * another, null);
        }

        @Override
        public int compareTo(End other) {
            if (beyond != 0 || other.beyond != 0) {
                return Integer.compare(beyond, other.beyond);
            }
            return at.compareTo(other.at);
        }
    }

    private final Expr root;
    private final Set<Term> places;
    private final Map<Term, Range> orders;

    private ComputedNumber(Expr root, Set<Term> places, Map<Term, Range> orders) {
        this.root = root;
        this.places = places;
        this.orders = orders;
    }

    /**
     * {@code term} read as arithmetic over places, or null where it is not wholly that or is
     * nothing but a place or a written number.
     *
     * <p>The order each step answers on is read when the number is, and kept with it: the type of
     * the value that step is, asked of the term it was read from. It is told neither from what the
     * step is made of nor from the type of the whole, because an operation can answer a type its
     * arguments are not — {@code Decimal.fromInt(a * b)} multiplies two whole numbers before it is
     * a decimal, {@code Decimal.fromInt(a) * Decimal.fromInt(b)} multiplies two decimals, and
     * {@code Decimal.toInt(d)} answers a whole number out of a decimal.
     *
     * @param aPlace  which terms are places of the value being read
     * @param orderOf the order the value of a term is counted on, as the range it runs over, or
     *                null where it is not known, which proves nothing
     */
    static ComputedNumber of(Term term, Predicate<Term> aPlace, Function<Term, Range> orderOf) {
        Set<Term> found = new LinkedHashSet<>();
        Expr read = read(term, aPlace, found);
        if (read == null || read instanceof Expr.Place || read instanceof Expr.Written
                || found.isEmpty()) {
            return null;
        }
        Map<Term, Range> orders = new HashMap<>();
        ordersOf(read, orderOf, orders);
        return new ComputedNumber(read, found, orders);
    }

    /** The places this number is made of, in the order they are first met. */
    Set<Term> places() {
        return places;
    }

    /**
     * What this comes to with each place at the number {@code at} gives it, or null where some
     * place has none, the arithmetic has no exact answer the host holds, or some step comes to a
     * number outside the order it answers on.
     *
     * <p>The one evaluation {@link #lies} is, with every place at a single number: a number the
     * arithmetic of its type aborts on is the answer of no run, so nothing is settled at it.
     */
    ExactRatio comesTo(Function<Term, ExactRatio> at) {
        Range whole = bounded(root, place -> {
            ExactRatio number = at.apply(place);
            return number == null ? null : Range.at(number);
        });
        return whole != null && whole.low() != null && whole.high() != null
                && whole.low().compareTo(whole.high()) == 0 ? whole.low() : null;
    }

    /**
     * Where this lies with each place in the range {@code at} gives it, or null where some step of
     * it can come to a number outside the order that step answers on, or where no order is known
     * for a step.
     *
     * <p>Every step and not only the last: the arithmetic of a type that stops somewhere aborts at
     * the step that leaves it, whatever the steps after it would have brought the number back to.
     *
     * @param at where each place lies, inside the order its numbers are on, or null where that
     *           order is not known
     */
    Range lies(Function<Term, Range> at) {
        return bounded(root, at);
    }

    /** The order of each step of {@code e}, as {@code orderOf} gives it for the term the step was
     *  read from. */
    private static void ordersOf(Expr e, Function<Term, Range> orderOf, Map<Term, Range> out) {
        switch (e) {
            case Expr.Place it -> out.put(it.term(), orderOf.apply(it.term()));
            case Expr.Written _ -> { }
            case Expr.Negated it -> {
                out.put(it.term(), orderOf.apply(it.term()));
                ordersOf(it.operand(), orderOf, out);
            }
            case Expr.Operated it -> {
                out.put(it.term(), orderOf.apply(it.term()));
                ordersOf(it.left(), orderOf, out);
                ordersOf(it.right(), orderOf, out);
            }
            case Expr.Weighed it -> {
                out.put(it.term(), orderOf.apply(it.term()));
                it.weights().forEach(each -> ordersOf(each.argument(), orderOf, out));
            }
            case Expr.Rounded it -> {
                out.put(it.term(), orderOf.apply(it.term()));
                ordersOf(it.inner(), orderOf, out);
            }
        }
    }

    private static Expr read(Term term, Predicate<Term> aPlace, Set<Term> found) {
        return switch (term.shape()) {
            case INT -> new Expr.Written(ExactRatio.of((Long) term.carried()));
            case DECIMAL -> new Expr.Written(ExactRatio.of((BigDecimal) term.carried()));
            case NEG -> negated(term, aPlace, found);
            case OP -> operated(term, aPlace, found);
            case CALLED -> called(term, aPlace, found);
            case AT, ON -> place(term, aPlace, found);
            default -> null;
        };
    }

    private static Expr negated(Term term, Predicate<Term> aPlace, Set<Term> found) {
        Expr operand = read(term.parts().getFirst(), aPlace, found);
        return operand == null ? null : new Expr.Negated(term, operand);
    }

    private static Expr operated(Term term, Predicate<Term> aPlace, Set<Term> found) {
        BinOp operator = (BinOp) term.carried();
        if (operator != BinOp.ADD && operator != BinOp.SUB && operator != BinOp.MUL) {
            return null;
        }
        Expr left = read(term.parts().get(0), aPlace, found);
        Expr right = left == null ? null : read(term.parts().get(1), aPlace, found);
        return right == null ? null : new Expr.Operated(term, operator, left, right);
    }

    private static Expr place(Term term, Predicate<Term> aPlace, Set<Term> found) {
        if (!aPlace.test(term)) {
            return null;
        }
        found.add(term);
        return new Expr.Place(term);
    }

    /** A call of an operation the library states the answer of: a form of its arguments, or a
     *  rounding of one of them to a step. */
    private static Expr called(Term term, Predicate<Term> aPlace, Set<Term> found) {
        ValueName operation = term.calledOperation();
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        LinearForm<DeclaredArgument> form = facts.answersAFormOfItsArguments(operation);
        if (form != null) {
            return weighed(term, form, aPlace, found);
        }
        BoundOperationFact.RoundsToAStep rounds = facts.roundsToAStep(operation);
        return rounds == null ? null : rounding(term, rounds, aPlace, found);
    }

    private static Expr weighed(Term term, LinearForm<DeclaredArgument> form,
                                Predicate<Term> aPlace, Set<Term> found) {
        List<Weight> weights = new ArrayList<>();
        for (Map.Entry<DeclaredArgument, ExactRatio> each : form.coefs().entrySet()) {
            Expr argument = argumentAt(term, each.getKey().position(), aPlace, found);
            if (argument == null) {
                return null;
            }
            weights.add(new Weight(each.getValue(), argument));
        }
        return new Expr.Weighed(term, form.constant(), List.copyOf(weights));
    }

    private static Expr rounding(Term term, BoundOperationFact.RoundsToAStep rounds,
                                 Predicate<Term> aPlace, Set<Term> found) {
        Long scale = rounds.scale() == null ? Long.valueOf(0)
                : term.parts().get(rounds.scale().position()).foldedWholeNumber();
        Term mode = term.parts().get(rounds.mode().position());
        WholeRounding way = mode.shape() == Term.Shape.UNIT
                ? rounds.ways().get((TypeSymbol) mode.carried()) : null;
        if (scale == null || way == null || !ARounding.answersAtAScale(BigInteger.valueOf(scale))) {
            return null;
        }
        Expr inner = argumentAt(term, rounds.value().position(), aPlace, found);
        return inner == null ? null
                : new Expr.Rounded(term, BigInteger.valueOf(scale), way, inner);
    }

    private static Expr argumentAt(Term call, int position, Predicate<Term> aPlace,
                                   Set<Term> found) {
        return position < call.parts().size()
                ? read(call.parts().get(position), aPlace, found) : null;
    }

    /**
     * Where {@code e} lies with each place in the range {@code at} gives it, or null where a step
     * of it can leave the order it answers on.
     *
     * <p>The one evaluation, for a range and for a single number alike: a step that is checked
     * against its order here is checked for every use of the number.
     */
    private Range bounded(Expr e, Function<Term, Range> at) {
        return switch (e) {
            case Expr.Place it -> stays(at.apply(it.term()), orders.get(it.term()));
            case Expr.Written it -> Range.at(it.number());
            case Expr.Negated it -> {
                Range operand = bounded(it.operand(), at);
                yield operand == null ? null : stays(operand.negated(), orders.get(it.term()));
            }
            case Expr.Operated it -> {
                Range left = bounded(it.left(), at);
                Range right = bounded(it.right(), at);
                if (left == null || right == null) {
                    yield null;
                }
                yield stays(switch (it.operator()) {
                    case ADD -> left.plus(right);
                    case SUB -> left.plus(right.negated());
                    case MUL -> left.times(right);
                    default -> throw new IllegalStateException("not arithmetic: " + it.operator());
                }, orders.get(it.term()));
            }
            case Expr.Weighed it -> {
                // Each argument on the order it is, and the weighed sum on the order it answers:
                // an operation that makes a decimal of a whole number takes the one and answers
                // the other.
                Range order = orders.get(it.term());
                Range sum = Range.at(it.constant());
                for (Weight each : it.weights()) {
                    Range argument = bounded(each.argument(), at);
                    Range weighed = argument == null ? null : stays(
                            argument.times(Range.at(each.coefficient())), order);
                    sum = weighed == null ? null : stays(sum.plus(weighed), order);
                    if (sum == null) {
                        break;
                    }
                }
                yield sum;
            }
            // Rounding to a step never turns a greater number into a lesser one, so the ends of
            // what is rounded are the ends of what it rounds to.
            case Expr.Rounded it -> {
                Range inner = bounded(it.inner(), at);
                yield inner == null ? null : stays(new Range(inner.low() == null ? null
                        : rounded(inner.low(), it.scale(), it.way()), inner.high() == null ? null
                        : rounded(inner.high(), it.scale(), it.way())), orders.get(it.term()));
            }
        };
    }

    /** {@code range} on {@code order}, or null where it reaches past it or either is not known. */
    private static Range stays(Range range, Range order) {
        if (range == null || order == null) {
            return null;
        }
        boolean low = order.low() == null
                || (range.low() != null && range.low().compareTo(order.low()) >= 0);
        boolean high = order.high() == null
                || (range.high() != null && range.high().compareTo(order.high()) <= 0);
        return low && high ? range : null;
    }

    /** {@code value} rounded to a whole multiple of ten to the minus {@code scale}, the way the
     *  run time rounds it. */
    private static ExactRatio rounded(ExactRatio value, BigInteger scale, WholeRounding way) {
        ExactRatio steps = ExactRatio.tenTo(scale.longValueExact());
        ExactRatio scaled = value.times(steps).orNull();
        if (scaled == null) {
            return null;
        }
        // A number on a step rounds to itself, and its steps are not written out to say so.
        if (scaled.isWhole()) {
            return value;
        }
        BigInteger whole = way.of(scaled);
        return whole == null ? null : ExactRatio.of(whole).dividedBy(steps).orNull();
    }
}
