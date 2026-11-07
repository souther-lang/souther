package souther.compiler.partition;

import souther.compiler.check.SeededWalk;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.InputNumber;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.WrittenOperation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;

import java.util.List;
import java.util.Map;

/**
 * What a walk's step, or a closure whose answers a total adds up, adds of each element it is
 * handed, as it is written: a path of the element, or paths of it multiplied, added to the answer
 * so far or taken from it. A run works out exactly those operations for each element, so the
 * reader of where a run stops knows them all: the sum or difference with the answer so far, and
 * the products.
 *
 * <p>Read off the tree and not off the form the arithmetic composes, which leaves out the
 * operations written to get to it: a product by one composes to the element, and is a product a
 * run works out all the same. And read off the total the number was read as ({@link #ofTheTotal}),
 * so that the two are asked to agree: a step written as this and a number read as that are the
 * same addend, and nothing is worked out of the element beside it.
 *
 * @param sign    one where each element's part is added, minus one where it is taken away
 * @param factors how many paths of the element are multiplied into the part, one where it is a
 *                path alone
 */
record AddedOfEachElement(int sign, int factors) {

    AddedOfEachElement {
        if (Math.abs(sign) != 1 || factors < 1) {
            throw new IllegalArgumentException("an element adds or takes away a path of it or a"
                    + " product of paths: " + sign + " " + factors);
        }
    }

    /**
     * What {@code walk}'s step adds of each element: the answer so far, on either side, plus a
     * part of the element, or the answer so far less one. Null where the step is anything else.
     */
    static AddedOfEachElement ofTheStep(SeededWalk walk, Symbols symbols) {
        BindingId carried = walk.accumulator().binding();
        BindingId element = walk.element().binding();
        Core body = walk.step().body();
        List<Core> sum = WrittenOperation.operandsOf(body, BinOp.ADD, symbols);
        if (sum != null) {
            return isRead(sum.get(0), carried) ? of(1, sum.get(1), element, symbols)
                    : isRead(sum.get(1), carried) ? of(1, sum.get(0), element, symbols) : null;
        }
        List<Core> difference = WrittenOperation.operandsOf(body, BinOp.SUB, symbols);
        return difference != null && isRead(difference.get(0), carried)
                ? of(-1, difference.get(1), element, symbols) : null;
    }

    /** What {@code closure} answers of the one element it is handed, as a part a total adds up;
     *  null where it answers anything else. */
    static AddedOfEachElement ofAClosure(Core.Block closure, Symbols symbols) {
        if (closure.params().size() != 1 || closure.params().getFirst() == null
                || closure.params().getFirst().binding() == null) {
            return null;
        }
        return of(1, closure.body(), closure.params().getFirst().binding(), symbols);
    }

    /**
     * What a total adds up of each element, where {@code term} is a total over a container of a
     * path of each element or one product of paths of it, at the weight one or minus one; null
     * where it is any other number.
     *
     * <p>The total of a walk joining two maps adds, for each entry of one, its value times what the
     * other files under its key or a nought written in its place: two numbers multiplied, as the
     * step that total is read of is written ({@link InputNumber#ofAWalkJoiningTwoMaps}).
     */
    static AddedOfEachElement ofTheTotal(NumericTerm term) {
        if (term instanceof NumericTerm.TakenOf taken) {
            return taken.takenAs() instanceof TakenAs.TheSumOfWhatItHolds
                    ? new AddedOfEachElement(1, 1) : null;
        }
        if (!(term instanceof NumericTerm.TakenOver over)
                || !(over.takenAs() instanceof TakenAs.TheSumOfWhatItHolds)) {
            return null;
        }
        if (over.source() instanceof RunSource.ProjectedOccurrences) {
            return new AddedOfEachElement(1, 1);
        }
        if (over.source() instanceof RunSource.JoinedOccurrences) {
            return new AddedOfEachElement(1, 2);
        }
        if (!(over.source() instanceof RunSource.ComputedOccurrences computed)) {
            return null;
        }
        return switch (computed.computation()) {
            case ElementValue.Affine affine when affine.form().constant().isZero()
                    && affine.form().coefs().size() == 1 ->
                    weighed(affine.form().coefs().values().iterator().next(), 1);
            case ElementValue.Multilinear product when product.form().constant().isZero()
                    && product.form().coefs().size() == 1 -> {
                Map.Entry<ElementValue.Monomial, ExactRatio> only =
                        product.form().coefs().entrySet().iterator().next();
                yield only.getKey().rounding() == null
                        ? weighed(only.getValue(), only.getKey().fields().size()) : null;
            }
            default -> null;
        };
    }

    private static AddedOfEachElement weighed(ExactRatio weight, int factors) {
        return ExactRatio.ONE.equals(weight) ? new AddedOfEachElement(1, factors)
                : ExactRatio.ONE.negated().equals(weight) ? new AddedOfEachElement(-1, factors)
                : null;
    }

    private static AddedOfEachElement of(int sign, Core part, BindingId element,
                                         Symbols symbols) {
        int factors = factorsOf(part, element, symbols);
        return factors < 1 ? null : new AddedOfEachElement(sign, factors);
    }

    /** How many paths of {@code element} {@code e} multiplies, or nought where it is anything
     *  but a path of it or a product of such. */
    private static int factorsOf(Core e, BindingId element, Symbols symbols) {
        List<Core> product = WrittenOperation.operandsOf(e, BinOp.MUL, symbols);
        if (product != null) {
            int left = factorsOf(product.get(0), element, symbols);
            int right = factorsOf(product.get(1), element, symbols);
            return left < 1 || right < 1 ? 0 : left + right;
        }
        return isAPathInside(e, element) ? 1 : 0;
    }

    /** Whether {@code e} is {@code element}, or fields of it one inside another. */
    private static boolean isAPathInside(Core e, BindingId element) {
        Core here = Core.withoutStanding(e);
        while (true) {
            switch (here) {
                case Core.Read read -> {
                    return element.equals(read.binding());
                }
                case Core.FieldAccess access -> here = Core.withoutStanding(access.target());
                case Core.FieldProjection projection ->
                        here = Core.withoutStanding(projection.base());
                default -> {
                    return false;
                }
            }
        }
    }

    private static boolean isRead(Core e, BindingId name) {
        return Core.withoutStanding(e) instanceof Core.Read read && name.equals(read.binding());
    }
}
