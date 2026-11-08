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

import java.math.BigInteger;
import java.util.List;
import java.util.Objects;
import java.util.function.Function;

/**
 * What a walk's step, or a closure whose answers a total adds up, works out of each element it is
 * handed, as it is written: paths of the element added, taken away and multiplied, and in a step
 * the answer so far that the rest is added to or taken from. A run works out exactly those
 * operations for each element, in the order the tree has them, so the reader of where a run stops
 * knows them all.
 *
 * <p>What the element comes to is not read here. That is the total's to say, read once by the
 * reading of the arithmetic ({@link ElementValue}), and two writings of one number are one number
 * there: {@code acc + p - q} and {@code acc + (p - q)} add the same to the answer. They are not one
 * piece of work. The first works out {@code acc + p} and takes {@code q} from it, the second works
 * out {@code p - q} and adds it, and each can stop a run the other gets through. So the tree is
 * read off the program and held as it is written, and every node of it is an operation, a path of
 * the element or the answer so far: a step that works out anything else, or reads a name, is not
 * read, and neither is a step whose answer so far is multiplied or taken away from something.
 *
 * <p>The tree is read only beside a total that adds up a number of each element
 * ({@link #addsUpEachElement}), which is the number the tree comes to.
 *
 * @param part what is worked out for each element
 */
record AddedOfEachElement(Part part) {

    AddedOfEachElement {
        Objects.requireNonNull(part, "what is worked out for each element");
        if (readsTheAnswerSoFar(part) && (!(part instanceof Worked) || !addsTo(part))) {
            throw new IllegalArgumentException("a step reads the answer so far once, added along"
                    + " sums and differences from the top to something of the element: " + part);
        }
    }

    /** A piece of what a step works out for each element. */
    sealed interface Part {}

    /** A path of the element, read as the row holds it: {@code l.p.value}. */
    record Path(Core read) implements Part {}

    /** A number of the row read where the total was, and not off this tree: what the other map of
     *  a walk joining two maps files under the key, or the nought written in its place. */
    record ReadWithTheTotal() implements Part {}

    /** The answer so far, where a walk's step adds to it or takes from it. */
    record SoFar() implements Part {}

    /** An operation of two parts, worked out once both are. */
    record Worked(BinOp op, Part left, Part right) implements Part {

        Worked {
            if (op != BinOp.ADD && op != BinOp.SUB && op != BinOp.MUL) {
                throw new IllegalArgumentException("an element's part is added, taken away or"
                        + " multiplied: " + op);
            }
        }
    }

    /**
     * What {@code walk}'s step works out of each element and the answer so far: the answer so far
     * added to, or taken from, a sum of parts of the element, each added or taken away in turn.
     * Null where the step is anything else, or reads the answer so far anywhere but there.
     */
    static AddedOfEachElement ofTheStep(SeededWalk walk, Symbols symbols) {
        Part part = partOf(walk.step().body(), walk.element().binding(),
                walk.accumulator().binding(), symbols);
        return part instanceof Worked && addsTo(part) ? new AddedOfEachElement(part) : null;
    }

    /** What {@code closure} works out of the one element it is handed, as a part a total adds up;
     *  null where it works out anything else. */
    static AddedOfEachElement ofAClosure(Core.Block closure, Symbols symbols) {
        if (closure.params().size() != 1 || closure.params().getFirst() == null
                || closure.params().getFirst().binding() == null) {
            return null;
        }
        Part part = partOf(closure.body(), closure.params().getFirst().binding(), null, symbols);
        return part == null ? null : new AddedOfEachElement(part);
    }

    /**
     * What the walk joining two maps works out of each entry, read where its total is read
     * ({@link InputNumber#ofAWalkJoiningTwoMaps}): the answer so far plus its value times what the
     * other map files under its key, or a nought written in its place.
     */
    static AddedOfEachElement ofAJoin() {
        return new AddedOfEachElement(new Worked(BinOp.ADD, new SoFar(),
                new Worked(BinOp.MUL, new ReadWithTheTotal(), new ReadWithTheTotal())));
    }

    /**
     * Whether {@code term} is a total over a container of a number of each element: what the
     * container holds, a path of each element, a number worked out of paths of each element with
     * nothing added beside them, or the walk joining two maps. What that number is worked out by
     * is asked of the tree ({@link #ofTheStep}, {@link #ofAClosure}).
     */
    static boolean addsUpEachElement(NumericTerm term) {
        if (term instanceof NumericTerm.TakenOf taken) {
            return taken.takenAs() instanceof TakenAs.TheSumOfWhatItHolds;
        }
        if (!(term instanceof NumericTerm.TakenOver over)
                || !(over.takenAs() instanceof TakenAs.TheSumOfWhatItHolds)) {
            return false;
        }
        return switch (over.source()) {
            case RunSource.ProjectedOccurrences _, RunSource.JoinedOccurrences _ -> true;
            case RunSource.ComputedOccurrences computed -> switch (computed.computation()) {
                case ElementValue.Affine affine -> affine.form().constant().isZero()
                        && !affine.form().coefs().isEmpty();
                case ElementValue.Multilinear product -> product.form().constant().isZero()
                        && !product.form().coefs().isEmpty()
                        && product.form().coefs().keySet().stream()
                        .allMatch(each -> each.rounding() == null);
                default -> false;
            };
            default -> false;
        };
    }

    /**
     * The most paths of the element any product on the way to a part multiplies, one where none
     * is multiplied. A number of a row is written at a bounded scale, a product is at the sum of
     * its factors' scales and a sum or a difference at the greater of its operands', so every
     * operation worked out of the element is at no more than this many times that bound.
     */
    int factors() {
        return factorsOf(part);
    }

    private static int factorsOf(Part part) {
        return switch (part) {
            case Path _, ReadWithTheTotal _, SoFar _ -> 1;
            case Worked(BinOp op, Part left, Part right) -> op == BinOp.MUL
                    ? factorsOf(left) + factorsOf(right)
                    : Math.max(factorsOf(left), factorsOf(right));
        };
    }

    /** How far the operations of a step over whole numbers are shown to get through. */
    enum Through {
        /** Every operation is held within the type on every row: none stops a run. */
        EVERY_ROW,
        /** Every operation is held within the type on a row of one element, or comes there to
         *  the total, which is told, and stops a run where the total does. */
        A_ROW_OF_ONE_ELEMENT,
        /** Some operation may stop a run where the total does not. */
        NOT_SHOWN
    }

    /**
     * How far the operations of whole numbers worked out for each element are shown to get
     * through, where the walk starts at {@code seed} — nought for a closure whose answers a total
     * adds up — and each path of the element comes to what {@code rangeOf} answers, null where
     * that is not known.
     *
     * <p>An operation gets through where every number it comes to lies within {@code least} and
     * {@code greatest}, from what its operands come to ({@link FormRange#combined}). On a row of
     * one element the answer so far is the seed, and the last operation is the total, which is
     * told and stops a run exactly where that number passes the ends; so does a part the answer
     * so far is added to where the seed is nought, since nought plus the part is the part. Where
     * an operation is held within the ends only on a row of one element, or only in coming to the
     * total, a row of more elements is not claimed. The answer so far on such a row is a running
     * total, and the operations worked out of it are the running totals' to answer for.
     */
    Through overWholeNumbers(BigInteger seed, Function<Core, FormRange> rangeOf,
                             BigInteger least, BigInteger greatest) {
        Checked checked = new Checker(seed, rangeOf, least, greatest).checked(part, true);
        return checked.notShown ? Through.NOT_SHOWN
                : checked.onOneElement ? Through.A_ROW_OF_ONE_ELEMENT : Through.EVERY_ROW;
    }

    /**
     * What a part comes to on a row of one element, whether an operation in it may stop a run
     * where the total does not ({@code notShown}), and whether one is shown to get through only on
     * such a row ({@code onOneElement}): one that reads the answer so far, which is the seed there
     * alone, or one that comes to the total.
     */
    private record Checked(FormRange range, boolean readsTheAnswerSoFar, boolean onOneElement,
                           boolean notShown) {}

    /** The asking of {@link #overWholeNumbers}, of each part in turn. */
    private record Checker(BigInteger seed, Function<Core, FormRange> rangeOf, BigInteger least,
                           BigInteger greatest) {

        /** {@code part} checked, where {@code theTotal} says it comes to the total on a row of
         *  one element: the whole of what is worked out, or a part the answer so far is added to
         *  there when the seed is nought. */
        Checked checked(Part part, boolean theTotal) {
            return switch (part) {
                case Path(Core read) -> new Checked(rangeOf.apply(read), false, false, false);
                case ReadWithTheTotal _ -> new Checked(null, false, false, false);
                case SoFar _ -> new Checked(new FormRange(ExactRatio.of(seed), ExactRatio.of(seed)),
                        true, false, false);
                case Worked(BinOp op, Part left, Part right) -> {
                    boolean addedToNought = theTotal && op == BinOp.ADD
                            && BigInteger.ZERO.equals(seed);
                    Checked l = checked(left, addedToNought && right instanceof SoFar);
                    Checked r = checked(right, addedToNought && left instanceof SoFar);
                    FormRange range = FormRange.combined(op, l.range, r.range);
                    boolean held = range != null && range.liesWithin(least, greatest);
                    boolean soFar = l.readsTheAnswerSoFar || r.readsTheAnswerSoFar;
                    yield new Checked(range, soFar,
                            l.onOneElement || r.onOneElement || soFar || (!held && theTotal),
                            l.notShown || r.notShown || (!held && !theTotal));
                }
            };
        }
    }

    private static boolean readsTheAnswerSoFar(Part part) {
        return switch (part) {
            case SoFar _ -> true;
            case Path _, ReadWithTheTotal _ -> false;
            case Worked worked ->
                    readsTheAnswerSoFar(worked.left()) || readsTheAnswerSoFar(worked.right());
        };
    }

    /** Whether {@code part} reads the answer so far once, added along a run of sums and
     *  differences from the top, and taken away from nothing. */
    private static boolean addsTo(Part part) {
        return switch (part) {
            case SoFar _ -> true;
            case Path _, ReadWithTheTotal _ -> false;
            case Worked(BinOp op, Part left, Part right) -> switch (op) {
                case ADD -> addsTo(left) ? !readsTheAnswerSoFar(right)
                        : addsTo(right) && !readsTheAnswerSoFar(left);
                case SUB -> addsTo(left) && !readsTheAnswerSoFar(right);
                default -> false;
            };
        };
    }

    /**
     * {@code e} as what it works out of {@code element}, and of the answer so far where
     * {@code carried} names it: a path of the element, the answer so far, or a sum, difference or
     * product of two such, written as the operator or as the library's operation. Null where any
     * node of it is anything else.
     */
    private static Part partOf(Core e, BindingId element, BindingId carried, Symbols symbols) {
        for (BinOp op : List.of(BinOp.ADD, BinOp.SUB, BinOp.MUL)) {
            List<Core> operands = WrittenOperation.operandsOf(e, op, symbols);
            if (operands != null) {
                Part left = partOf(operands.get(0), element, carried, symbols);
                Part right = left == null ? null
                        : partOf(operands.get(1), element, carried, symbols);
                return right == null ? null : new Worked(op, left, right);
            }
        }
        if (carried != null && Core.withoutStanding(e) instanceof Core.Read read
                && carried.equals(read.binding())) {
            return new SoFar();
        }
        return isAPathInside(e, element) ? new Path(e) : null;
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
}
