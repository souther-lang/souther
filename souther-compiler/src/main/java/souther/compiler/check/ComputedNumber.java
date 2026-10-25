package souther.compiler.check;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.BinOp;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
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

        record Negated(Expr operand) implements Expr {}

        record Operated(BinOp operator, Expr left, Expr right) implements Expr {}

        /** A constant and each argument at its weight, as the library states an answer. */
        record Weighed(ExactRatio constant, List<Weight> weights) implements Expr {}

        record Rounded(BigInteger scale, WholeRounding way, Expr inner) implements Expr {}
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

    private ComputedNumber(Expr root, Set<Term> places) {
        this.root = root;
        this.places = places;
    }

    /**
     * {@code term} read as arithmetic over places, or null where it is not wholly that or is
     * nothing but a place or a written number.
     *
     * @param aPlace which terms are places of the value being read
     */
    static ComputedNumber of(Term term, Predicate<Term> aPlace) {
        Set<Term> found = new LinkedHashSet<>();
        Expr read = read(term, aPlace, found);
        if (read == null || read instanceof Expr.Place || read instanceof Expr.Written
                || found.isEmpty()) {
            return null;
        }
        return new ComputedNumber(read, found);
    }

    /** The places this number is made of, in the order they are first met. */
    Set<Term> places() {
        return places;
    }

    /**
     * What this comes to with each place at the number {@code at} gives it, or null where some
     * place has none or the arithmetic has no exact answer the host holds.
     */
    ExactRatio comesTo(Function<Term, ExactRatio> at) {
        return evaluate(root, at);
    }

    /**
     * Where this lies with each place in the range {@code at} gives it. A range of every number
     * wherever the arithmetic cannot say better.
     */
    Range lies(Function<Term, Range> at) {
        return bounded(root, at);
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
        return operand == null ? null : new Expr.Negated(operand);
    }

    private static Expr operated(Term term, Predicate<Term> aPlace, Set<Term> found) {
        BinOp operator = (BinOp) term.carried();
        if (operator != BinOp.ADD && operator != BinOp.SUB && operator != BinOp.MUL) {
            return null;
        }
        Expr left = read(term.parts().get(0), aPlace, found);
        Expr right = left == null ? null : read(term.parts().get(1), aPlace, found);
        return right == null ? null : new Expr.Operated(operator, left, right);
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
        return new Expr.Weighed(form.constant(), List.copyOf(weights));
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
        return inner == null ? null : new Expr.Rounded(BigInteger.valueOf(scale), way, inner);
    }

    private static Expr argumentAt(Term call, int position, Predicate<Term> aPlace,
                                   Set<Term> found) {
        return position < call.parts().size()
                ? read(call.parts().get(position), aPlace, found) : null;
    }

    private static ExactRatio evaluate(Expr e, Function<Term, ExactRatio> at) {
        return switch (e) {
            case Expr.Place it -> at.apply(it.term());
            case Expr.Written it -> it.number();
            case Expr.Negated it -> {
                ExactRatio operand = evaluate(it.operand(), at);
                yield operand == null ? null : operand.negated();
            }
            case Expr.Operated it -> {
                ExactRatio left = evaluate(it.left(), at);
                ExactRatio right = left == null ? null : evaluate(it.right(), at);
                if (right == null) {
                    yield null;
                }
                yield (switch (it.operator()) {
                    case ADD -> left.plus(right);
                    case SUB -> left.minus(right);
                    case MUL -> left.times(right);
                    default -> throw new IllegalStateException("not arithmetic: " + it.operator());
                }).orNull();
            }
            case Expr.Weighed it -> {
                ExactRatio sum = it.constant();
                for (Weight each : it.weights()) {
                    ExactRatio argument = evaluate(each.argument(), at);
                    ExactRatio weighed = argument == null ? null
                            : argument.times(each.coefficient()).orNull();
                    sum = weighed == null ? null : sum.plus(weighed).orNull();
                    if (sum == null) {
                        break;
                    }
                }
                yield sum;
            }
            case Expr.Rounded it -> {
                ExactRatio value = evaluate(it.inner(), at);
                yield value == null ? null : rounded(value, it.scale(), it.way());
            }
        };
    }

    private static Range bounded(Expr e, Function<Term, Range> at) {
        return switch (e) {
            case Expr.Place it -> at.apply(it.term());
            case Expr.Written it -> Range.at(it.number());
            case Expr.Negated it -> bounded(it.operand(), at).negated();
            case Expr.Operated it -> {
                Range left = bounded(it.left(), at);
                Range right = bounded(it.right(), at);
                yield switch (it.operator()) {
                    case ADD -> left.plus(right);
                    case SUB -> left.plus(right.negated());
                    case MUL -> left.times(right);
                    default -> throw new IllegalStateException("not arithmetic: " + it.operator());
                };
            }
            case Expr.Weighed it -> {
                Range sum = Range.at(it.constant());
                for (Weight each : it.weights()) {
                    sum = sum.plus(bounded(each.argument(), at)
                            .times(Range.at(each.coefficient())));
                }
                yield sum;
            }
            // Rounding to a step never turns a greater number into a lesser one, so the ends of
            // what is rounded are the ends of what it rounds to.
            case Expr.Rounded it -> {
                Range inner = bounded(it.inner(), at);
                yield new Range(inner.low() == null ? null : rounded(inner.low(), it.scale(),
                        it.way()), inner.high() == null ? null
                        : rounded(inner.high(), it.scale(), it.way()));
            }
        };
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
