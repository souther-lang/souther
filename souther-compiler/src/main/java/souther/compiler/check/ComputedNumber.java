package souther.compiler.check;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.types.BinOp;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * A number a clause writes as exact arithmetic over places: sums, differences and products, a
 * whole number taken as a decimal, and a decimal rounded to a scale.
 *
 * <p>What a place comes to decides what this comes to, and nothing else does: with every place at
 * one number the arithmetic answers one number, exactly, the way the run time answers it. That is
 * all this reads. It states no range for the number and no relation of it to a place, because the
 * interval algebra has atoms for a number and rules between atoms, and a number made of places is
 * one more atom whose rule to them is this.
 *
 * <p>Only what is written wholly of those. A call to anything else, a quotient, a choice or a place
 * that is not a place of the value leaves the number unread, and the clause is not taken in
 * through it.
 */
final class ComputedNumber {

    private static final ValueName.Stdlib ROUND = ValueName.Stdlib.operation("Decimal", "round");
    private static final ValueName.Stdlib FROM_INT = ValueName.Stdlib.operation("Decimal", "fromInt");

    /** What is computed: a place, a written number, or an operation over those. */
    private sealed interface Expr {

        record Place(Term term) implements Expr {}

        record Written(ExactRatio number) implements Expr {}

        record Negated(Expr operand) implements Expr {}

        record Operated(BinOp operator, Expr left, Expr right) implements Expr {}

        record Rounded(BigInteger scale, WholeRounding way, Expr inner) implements Expr {}
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

    private static Expr read(Term term, Predicate<Term> aPlace, Set<Term> found) {
        switch (term.shape()) {
            case INT -> {
                return new Expr.Written(ExactRatio.of((Long) term.carried()));
            }
            case DECIMAL -> {
                return new Expr.Written(ExactRatio.of((BigDecimal) term.carried()));
            }
            case NEG -> {
                Expr operand = read(term.parts().getFirst(), aPlace, found);
                return operand == null ? null : new Expr.Negated(operand);
            }
            case OP -> {
                BinOp operator = (BinOp) term.carried();
                if (operator != BinOp.ADD && operator != BinOp.SUB && operator != BinOp.MUL) {
                    return null;
                }
                Expr left = read(term.parts().get(0), aPlace, found);
                Expr right = left == null ? null : read(term.parts().get(1), aPlace, found);
                return right == null ? null : new Expr.Operated(operator, left, right);
            }
            case CALLED -> {
                return called(term, aPlace, found);
            }
            case AT, ON -> {
                if (!aPlace.test(term)) {
                    return null;
                }
                found.add(term);
                return new Expr.Place(term);
            }
            default -> {
                return null;
            }
        }
    }

    private static Expr called(Term term, Predicate<Term> aPlace, Set<Term> found) {
        if (FROM_INT.equals(term.calledOperation()) && term.parts().size() == 1) {
            return read(term.parts().getFirst(), aPlace, found);
        }
        if (!ROUND.equals(term.calledOperation()) || term.parts().size() != 3) {
            return null;
        }
        Long scale = term.parts().get(0).foldedWholeNumber();
        WholeRounding way = wayWritten(term.parts().get(1));
        if (scale == null || way == null || !ARounding.answersAtAScale(BigInteger.valueOf(scale))) {
            return null;
        }
        Expr inner = read(term.parts().get(2), aPlace, found);
        return inner == null ? null : new Expr.Rounded(BigInteger.valueOf(scale), way, inner);
    }

    /** The way of rounding a case of the library's policy is, or null where {@code mode} is not
     *  one written out. */
    private static WholeRounding wayWritten(Term mode) {
        if (mode.shape() != Term.Shape.UNIT) {
            return null;
        }
        String name = ((TypeSymbol) mode.carried()).name();
        for (WholeRounding way : WholeRounding.values()) {
            if (way.name().equals(name)) {
                return way;
            }
        }
        return null;
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
            case Expr.Rounded it -> {
                ExactRatio value = evaluate(it.inner(), at);
                yield value == null ? null : rounded(value, it.scale(), it.way());
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
