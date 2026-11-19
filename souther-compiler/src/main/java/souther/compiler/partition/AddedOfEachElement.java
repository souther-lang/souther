package souther.compiler.partition;

import souther.compiler.check.Comparison;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ElementAnswer;
import souther.compiler.check.SeededWalk;
import souther.compiler.core.Core;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.InputNumber;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.WrittenOperation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * What a walk's step, or a closure whose answers a total adds up, works out of each element it is
 * handed, as it is written: paths of the element and numbers written out, added, taken away and
 * multiplied, the values its names are given, and in a step the answer so far that the rest is
 * added to or taken from. A run works out exactly those operations for each element, in the order
 * they are written, so the reader of where a run stops knows them all.
 *
 * <p>What the element comes to is not read here. That is the total's to say, read once by the
 * reading of the arithmetic ({@link ElementValue}), and two writings of one number are one number
 * there: {@code acc + p - q} and {@code acc + (p - q)} add the same to the answer. They are not one
 * piece of work. The first works out {@code acc + p} and takes {@code q} from it, the second works
 * out {@code p - q} and adds it, and each can stop a run the other gets through. So the tree is
 * read off the program and held as it is written.
 *
 * <p>Every value a name is given is worked out before what follows, whether anything reads it or
 * not, and is held here in the order the names are given ({@code bound}); a read of the name is a
 * read of that value and works out nothing again. A step or closure that works out anything but
 * these — a call of any other operation, a name it was not given here, a choice where a reader
 * did not say what decides it ends no run — is not read, and neither is a step whose answer so far
 * is multiplied, taken away from something, or given to a name.
 *
 * <p>The tree is read only beside a total that adds up a number of each element
 * ({@link #addsUpEachElement}), which is the number the tree comes to.
 *
 * @param bound   the values the names of the step are given, in the order they are given
 * @param aliases what each name given a path of the element stands for, which a path read
 *                through the name is read with ({@link Path})
 * @param answer  what the step answers for each element
 */
record AddedOfEachElement(List<Bound> bound, Map<BindingId, Core> aliases, Part answer) {

    AddedOfEachElement {
        bound = List.copyOf(bound);
        // In the order the names were given, which a reader handed it may walk it in.
        aliases = Collections.unmodifiableMap(new LinkedHashMap<>(aliases));
        Objects.requireNonNull(answer, "what is worked out for each element");
        for (Bound each : bound) {
            if (readsTheAnswerSoFar(each.value())) {
                throw new IllegalArgumentException("the answer so far is given to no name: "
                        + each);
            }
        }
        if (readsTheAnswerSoFar(answer)
                && (!(answer instanceof Worked || answer instanceof Chosen) || !addsTo(answer))) {
            throw new IllegalArgumentException("a step reads the answer so far once, added along"
                    + " sums and differences from the top to something of the element: "
                    + answer);
        }
    }

    /** What {@code answer} works out with no name given. */
    AddedOfEachElement(Part answer) {
        this(List.of(), Map.of(), answer);
    }

    /** A piece of what a step works out for each element. */
    sealed interface Part {}

    /** A path of the element, read as the row holds it: {@code l.p.value}, or a field read off a
     *  name given a path ({@link #aliases}). */
    record Path(Core read) implements Part {}

    /** A number written out: a whole number or a decimal, at the scale it is written. */
    record Written(BigDecimal value) implements Part {

        Written {
            Objects.requireNonNull(value, "a number written out");
        }
    }

    /** The value a name of the step was given ({@link Bound}), read where the name is. */
    record Named(BindingId name) implements Part {

        Named {
            Objects.requireNonNull(name, "a name the step gave a value");
        }
    }

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

    /** A choice between arms, whichever a run takes: read only where what decides it ends no
     *  run. In a step each arm adds to the answer so far, is it, or reads it nowhere. */
    record Chosen(List<Taken> arms) implements Part {

        Chosen {
            arms = List.copyOf(arms);
        }
    }

    /** One arm of a choice, and what deciding it states of a path of the element; null where it
     *  states nothing a path's numbers are held to. */
    record Taken(Part answers, Narrowed where) {

        Taken {
            Objects.requireNonNull(answers, "what the arm answers");
        }
    }

    /**
     * That an arm is taken only where the whole numbers of a path of the element ({@code path})
     * stand in {@code rel} to {@code number}; {@code samePlace} says whether another path reads
     * the same place of the element.
     */
    record Narrowed(Core path, Predicate<Core> samePlace, Rel rel, ExactRatio number) {}

    /** A name the step gives a value, and the value, worked out where it is given. */
    record Bound(BindingId name, Part value) {

        Bound {
            Objects.requireNonNull(name, "a name");
            Objects.requireNonNull(value, "the value it is given");
        }
    }

    /**
     * What {@code walk}'s step works out of each element and the answer so far: the answer so far
     * added to, or taken from, what is worked out of the element. Null where the step is anything
     * else, or reads the answer so far anywhere but there.
     */
    static AddedOfEachElement ofTheStep(SeededWalk walk) {
        AddedOfEachElement read = new Reader(walk.element().binding(),
                walk.accumulator().binding()).read(walk.step().body());
        return read != null && read.answer() instanceof Worked && addsTo(read.answer())
                ? read : null;
    }

    /**
     * The same, a choice read arm by arm where what decides it ends no run
     * ({@code decidesWithoutAStop}), each arm adding to the answer so far or being it and taken
     * where its condition holds of a place of the element ({@code newtypes} tell which), for
     * asking where every number the walk works out lies ({@link #heldOverEveryStep}).
     */
    static AddedOfEachElement ofTheStep(SeededWalk walk, Predicate<Core> decidesWithoutAStop,
                                        DeclarationNewtypes newtypes) {
        return new Reader(walk.element().binding(), walk.accumulator().binding(), null,
                decidesWithoutAStop, newtypes).read(walk.step().body());
    }

    /** What {@code closure} works out of the one element it is handed, as a part a total adds up;
     *  null where it works out anything else. */
    static AddedOfEachElement ofAClosure(Core.Block closure) {
        if (closure.params().size() != 1 || closure.params().getFirst() == null
                || closure.params().getFirst().binding() == null) {
            return null;
        }
        return new Reader(closure.params().getFirst().binding(), null).read(closure.body());
    }

    /**
     * What a closure applied to each element works out of it ({@code answer}), the position it is
     * handed read as a path, and a choice read arm by arm where what decides it ends no run
     * ({@code decidesWithoutAStop}), each arm taken where its condition holds of a place of the
     * element ({@code newtypes} tell which). Null where it works out anything else.
     */
    static AddedOfEachElement ofAnAnswer(ElementAnswer answer,
                                         Predicate<Core> decidesWithoutAStop,
                                         DeclarationNewtypes newtypes) {
        return new Reader(answer.parameter(), null, answer.position(), decidesWithoutAStop,
                newtypes).read(answer.body());
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
     * container holds, a path of each element, a number worked out of paths of each element and
     * numbers written out, or the walk joining two maps. What that number is worked out by is
     * asked of the tree ({@link #ofTheStep}, {@link #ofAClosure}).
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
                case ElementValue.Affine affine -> !affine.form().coefs().isEmpty();
                case ElementValue.Multilinear product -> !product.form().coefs().isEmpty()
                        && product.form().coefs().keySet().stream()
                        .allMatch(each -> each.rounding() == null);
                default -> false;
            };
            default -> false;
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
     * one element the answer so far is the seed, and the answer is the total, which is told and
     * stops a run exactly where that number passes the ends; so does a part the answer so far is
     * added to where the seed is nought, since nought plus the part is the part, and the value of
     * a name that is the whole of such a part. Where an operation is held within the ends only on
     * a row of one element, or only in coming to the total, a row of more elements is not claimed.
     * The answer so far on such a row is a running total, and the operations worked out of it are
     * the running totals' to answer for — save where the step moves the answer so far one way
     * only ({@link #movesOneWay}), when every running total lies between the seed and the answer
     * and every row is claimed.
     */
    Through overWholeNumbers(BigInteger seed, Function<Core, FormRange> rangeOf,
                             BigInteger least, BigInteger greatest) {
        Checker checker = new Checker(seed, rangeOf, least, greatest, new HashMap<>());
        BindingId theTotal = nameThatIsTheTotal(seed);
        boolean notShown = false;
        boolean onOneElement = false;
        for (Bound each : bound) {
            Checked value = checker.checked(each.value(), each.name().equals(theTotal));
            checker.named().put(each.name(), value);
            notShown |= value.notShown();
            onOneElement |= value.onOneElement();
        }
        Checked whole = checker.checked(answer, true);
        if (notShown || whole.notShown()) {
            return Through.NOT_SHOWN;
        }
        if (!onOneElement && movesOneWay(checker)) {
            return Through.EVERY_ROW;
        }
        return onOneElement || whole.onOneElement() ? Through.A_ROW_OF_ONE_ELEMENT
                : Through.EVERY_ROW;
    }

    /**
     * Whether every operation of whole numbers worked out for an element, the answer's own among
     * them, lies within {@code least} and {@code greatest}, each path of the element coming to
     * what {@code rangeOf} answers: then working the closure out ends no run on any element. Of a
     * closure, which reads no answer so far.
     */
    boolean holdsEveryOperation(Function<Core, FormRange> rangeOf, BigInteger least,
                                BigInteger greatest) {
        return checkedAlone(rangeOf, least, greatest) != null;
    }

    /**
     * The numbers the answer for an element comes to, where every operation worked out for it is
     * held as {@link #holdsEveryOperation} asks; null where one is not, or where what the answer
     * comes to is not known.
     */
    FormRange answerHeldWithin(Function<Core, FormRange> rangeOf, BigInteger least,
                               BigInteger greatest) {
        Checked whole = checkedAlone(rangeOf, least, greatest);
        return whole == null ? null : whole.range();
    }

    /**
     * Whether every number a walk's step works out, from {@code seed} over at most {@code most}
     * elements, lies within {@code least} and {@code greatest}, each path of the element coming to
     * what {@code rangeOf} answers. Each step moves the answer so far by what it adds, which lies
     * within a range of its own; after any number of steps up to {@code most} the answer so far
     * lies within the seed and that many times the range either way, and each operation of a step
     * is asked with the answer so far anywhere there.
     *
     * <p>A step that may answer afresh ({@link #answersAfresh}) answers, read with the answer so
     * far nought, a value within the same range, and what follows it adds to that value: the
     * answer so far is then a sum of as many such values as steps were taken, and lies within
     * nought or the seed and that many times the range.
     */
    boolean heldOverEveryStep(BigInteger seed, Function<Core, FormRange> rangeOf, long most,
                              BigInteger least, BigInteger greatest) {
        FormRange none = new FormRange(ExactRatio.ZERO, ExactRatio.ZERO);
        Checked moved = checkedAlone(none, rangeOf, least, greatest, true);
        if (moved == null || moved.range() == null) {
            return false;
        }
        FormRange steps = new FormRange(ExactRatio.ZERO, ExactRatio.of(most));
        FormRange reached = FormRange.combined(BinOp.MUL, moved.range().hull(none), steps);
        FormRange from = new FormRange(ExactRatio.of(seed), ExactRatio.of(seed));
        FormRange soFar = reached == null ? null : FormRange.combined(BinOp.ADD, reached,
                answersAfresh(answer) ? from.hull(none) : from);
        return soFar != null && soFar.liesWithin(least, greatest)
                && checkedAlone(soFar, rangeOf, least, greatest, false) != null;
    }

    /** What the answer comes to, each operation asked on its own and none taken to come to a
     *  total; null where one may stop a run. */
    private Checked checkedAlone(Function<Core, FormRange> rangeOf, BigInteger least,
                                 BigInteger greatest) {
        Checked whole = checkedAlone(new FormRange(ExactRatio.ZERO, ExactRatio.ZERO), rangeOf,
                least, greatest, false);
        return whole == null || whole.readsTheAnswerSoFar() ? null : whole;
    }

    /** The same with the answer so far anywhere in {@code soFar}, and, where {@code onlyItsRange},
     *  what the answer comes to whether or not an operation on the way may stop a run. */
    private Checked checkedAlone(FormRange soFar, Function<Core, FormRange> rangeOf,
                                 BigInteger least, BigInteger greatest, boolean onlyItsRange) {
        Checker checker = new Checker(BigInteger.ZERO, soFar, rangeOf, least, greatest,
                new HashMap<>());
        for (Bound each : bound) {
            Checked value = checker.checked(each.value(), false);
            if (value.notShown() && !onlyItsRange) {
                return null;
            }
            checker.named().put(each.name(), value);
        }
        Checked whole = checker.checked(answer, false);
        return whole.notShown() && !onlyItsRange ? null : whole;
    }

    /**
     * Whether a walk's step moves the answer so far one way only, by what gets through on every
     * row: the answer so far with a part of the element added or taken away, each operation of
     * the part within the ends on every row, and the part never past nought on one side. Every
     * answer so far then lies between the seed and the answer, and where those are within the
     * ends, so is every one, on a row of any number of elements. A step that works the answer so
     * far out twice ({@code acc + p - q}) is not one: what it works out on the way lies past both.
     */
    private boolean movesOneWay(Checker checker) {
        if (!(answer instanceof Worked(BinOp op, Part left, Part right))
                || (op != BinOp.ADD && op != BinOp.SUB)) {
            return false;
        }
        Part moved = left instanceof SoFar ? right
                : op == BinOp.ADD && right instanceof SoFar ? left : null;
        if (moved == null || readsTheAnswerSoFar(moved)) {
            return false;
        }
        Checked part = checker.checked(moved, false);
        FormRange range = part.range();
        return !part.notShown() && !part.onOneElement() && range != null
                && (range.least().signum() >= 0 || range.greatest().signum() <= 0);
    }

    /** The name whose value comes to the total on a row of one element, where the answer is that
     *  name, or that name added to the answer so far from nought; null where none is. */
    private BindingId nameThatIsTheTotal(BigInteger seed) {
        Part total = answer;
        if (BigInteger.ZERO.equals(seed) && answer instanceof Worked(BinOp op, Part left, Part right)
                && op == BinOp.ADD) {
            total = left instanceof SoFar ? right : right instanceof SoFar ? left : answer;
        }
        return total instanceof Named(BindingId name) ? name : null;
    }

    /**
     * What a part comes to on a row of one element, whether it reads the answer so far, whether
     * an operation in it may stop a run where the total does not ({@code notShown}), and whether
     * one is shown to get through only on such a row ({@code onOneElement}): one that reads the
     * answer so far, which is the seed there alone, or one that comes to the total.
     */
    private record Checked(FormRange range, boolean readsTheAnswerSoFar, boolean onOneElement,
                           boolean notShown) {}

    /** The asking of {@link #overWholeNumbers}, of each part in turn, with what each name given
     *  so far was found to come to; the answer so far is the seed, or every number of
     *  {@code soFar} where that is given. */
    private record Checker(BigInteger seed, FormRange soFar, Function<Core, FormRange> rangeOf,
                           BigInteger least, BigInteger greatest, Map<BindingId, Checked> named) {

        Checker(BigInteger seed, Function<Core, FormRange> rangeOf, BigInteger least,
                BigInteger greatest, Map<BindingId, Checked> named) {
            this(seed, new FormRange(ExactRatio.of(seed), ExactRatio.of(seed)), rangeOf, least,
                    greatest, named);
        }

        /** The same asking inside an arm taken only where {@code where} holds: the path it is
         *  about comes to the numbers there; null where it comes to none and no run takes the
         *  arm. */
        Checker taken(Narrowed where) {
            FormRange whole = rangeOf.apply(where.path());
            if (whole != null && whole.heldTo(where.rel(), where.number()) == null) {
                return null;
            }
            Function<Core, FormRange> narrowed = path -> {
                FormRange range = rangeOf.apply(path);
                return range != null && where.samePlace().test(path)
                        ? range.heldTo(where.rel(), where.number()) : range;
            };
            return new Checker(seed, soFar, narrowed, least, greatest, named);
        }

        /** {@code part} checked, where {@code theTotal} says it comes to the total on a row of
         *  one element: the whole of what is worked out, or a part the answer so far is added to
         *  there when the seed is nought. A name read works out nothing again. */
        Checked checked(Part part, boolean theTotal) {
            return switch (part) {
                case Path(Core read) -> new Checked(rangeOf.apply(read), false, false, false);
                case Written(BigDecimal value) -> new Checked(
                        new FormRange(ExactRatio.of(value), ExactRatio.of(value)), false, false,
                        false);
                case Named(BindingId name) -> {
                    Checked value = named.get(name);
                    yield new Checked(value.range(), value.readsTheAnswerSoFar(), false, false);
                }
                case ReadWithTheTotal _ -> new Checked(null, false, false, false);
                case Chosen(List<Taken> arms) -> {
                    FormRange hull = null;
                    boolean known = true;
                    boolean soFar = false;
                    boolean onOneElement = false;
                    boolean notShown = false;
                    for (Taken arm : arms) {
                        Checker in = arm.where() == null ? this : taken(arm.where());
                        if (in == null) {
                            continue;
                        }
                        Checked one = in.checked(arm.answers(), theTotal);
                        known &= one.range() != null;
                        hull = !known ? null : hull == null ? one.range() : hull.hull(one.range());
                        soFar |= one.readsTheAnswerSoFar();
                        onOneElement |= one.onOneElement();
                        notShown |= one.notShown();
                    }
                    yield new Checked(hull, soFar, onOneElement, notShown);
                }
                case SoFar _ -> new Checked(soFar, true, false, false);
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

    /** Whether some arm of {@code part}, a choice, reads the answer so far nowhere: a step taking
     *  it answers afresh, whatever the answer so far was. */
    private static boolean answersAfresh(Part part) {
        return part instanceof Chosen chosen && chosen.arms().stream()
                .anyMatch(arm -> !readsTheAnswerSoFar(arm.answers()));
    }

    private static boolean readsTheAnswerSoFar(Part part) {
        return switch (part) {
            case SoFar _ -> true;
            case Path _, Written _, Named _, ReadWithTheTotal _ -> false;
            case Worked worked ->
                    readsTheAnswerSoFar(worked.left()) || readsTheAnswerSoFar(worked.right());
            case Chosen chosen -> chosen.arms().stream()
                    .anyMatch(arm -> readsTheAnswerSoFar(arm.answers()));
        };
    }

    /** Whether {@code part} reads the answer so far once, added along a run of sums and
     *  differences from the top, and taken away from nothing. An arm of a choice may instead read
     *  it nowhere, and answer afresh ({@link #answersAfresh}). */
    private static boolean addsTo(Part part) {
        return switch (part) {
            case SoFar _ -> true;
            case Path _, Written _, Named _, ReadWithTheTotal _ -> false;
            case Chosen chosen -> chosen.arms().stream().allMatch(arm -> addsTo(arm.answers())
                    || !readsTheAnswerSoFar(arm.answers()));
            case Worked(BinOp op, Part left, Part right) -> switch (op) {
                case ADD -> addsTo(left) ? !readsTheAnswerSoFar(right)
                        : addsTo(right) && !readsTheAnswerSoFar(left);
                case SUB -> addsTo(left) && !readsTheAnswerSoFar(right);
                default -> false;
            };
        };
    }

    /**
     * The reading of one step or closure: what it works out of {@code element}, and of the answer
     * so far where {@code carried} names it, with the names it gives values on the way.
     */
    private static final class Reader {

        private final BindingId element;
        private final BindingId carried;
        /** The position the closure is handed, read as a path; null where it is handed none. */
        private final BindingId position;
        /** Whether what decides a choice ends no run, where a choice is read; none where it is
         *  not. */
        private final Predicate<Core> decidesWithoutAStop;
        /** What tells which place of the element a path reads, for what deciding an arm states
         *  of it; null where nothing is asked of that. */
        private final DeclarationNewtypes newtypes;
        private final List<Bound> bound = new ArrayList<>();
        /** What each name given so far stands for, where it is a path of the element. */
        private final Map<BindingId, Core> paths = new LinkedHashMap<>();

        Reader(BindingId element, BindingId carried) {
            this(element, carried, null, _ -> false, null);
        }

        Reader(BindingId element, BindingId carried, BindingId position,
               Predicate<Core> decidesWithoutAStop, DeclarationNewtypes newtypes) {
            this.element = element;
            this.carried = carried;
            this.position = position;
            this.decidesWithoutAStop = decidesWithoutAStop;
            this.newtypes = newtypes;
        }

        /** {@code body} as what it works out, or null where any of it is anything else, or it
         *  reads the answer so far but to add to it. */
        AddedOfEachElement read(Core body) {
            Part answer = partOf(body);
            if (answer == null || (readsTheAnswerSoFar(answer)
                    && (!(answer instanceof Worked || answer instanceof Chosen)
                            || !addsTo(answer)))) {
                return null;
            }
            return new AddedOfEachElement(bound, paths, answer);
        }

        /**
         * {@code e} as what it works out: a path of the element, a number written out, a name
         * given here, the answer so far, or a sum, difference or product of two such, written as
         * the operator or as the library's operation. A name given a value is given it before
         * what follows, which is read with the name. Null where any node is anything else.
         */
        private Part partOf(Core e) {
            Core bare = Core.withoutStanding(e);
            for (BinOp op : List.of(BinOp.ADD, BinOp.SUB, BinOp.MUL)) {
                List<Core> operands = WrittenOperation.operandsOf(bare, op);
                if (operands != null) {
                    Part left = partOf(operands.get(0));
                    Part right = left == null ? null : partOf(operands.get(1));
                    return right == null ? null : new Worked(op, left, right);
                }
            }
            if (bare instanceof Core.LetIn let) {
                return given(let) ? partOf(let.body()) : null;
            }
            if (bare instanceof Core.If fork && decidesWithoutAStop.test(fork.cond())) {
                Narrowed holding = narrowedBy(fork.cond());
                return chosen(List.of(fork.then(), fork.els()), Arrays.asList(holding,
                        holding == null ? null : new Narrowed(holding.path(),
                                holding.samePlace(), holding.rel().denied(), holding.number())));
            }
            if (bare instanceof Core.Match match && decidesWithoutAStop.test(match.scrutinee())) {
                List<Core> arms = match.cases().stream().map(Core.Case::body).toList();
                return chosen(arms, Collections.nCopies(arms.size(), null));
            }
            if (bare instanceof Core.Read read && read.binding() != null) {
                if (read.binding().equals(carried)) {
                    return new SoFar();
                }
                if (!paths.containsKey(read.binding()) && isGiven(read.binding())) {
                    return new Named(read.binding());
                }
            }
            // A negation is an operation and stops a run where it passes the type, as nought less
            // the number does: the least whole number has no negation.
            if (bare instanceof Core.Neg negated) {
                Part operand = partOf(negated.operand());
                return operand == null ? null
                        : new Worked(BinOp.SUB, new Written(BigDecimal.ZERO), operand);
            }
            BigDecimal written = writtenOut(bare);
            if (written != null) {
                return new Written(written);
            }
            return isAPathInside(bare) ? new Path(e) : null;
        }

        /** A choice between {@code arms}, each read as a part and taken where {@code where} says
         *  ({@link Taken}); null where one is not read. A name an arm binds is no part, so an arm
         *  reading one is not read. */
        private Part chosen(List<Core> arms, List<Narrowed> where) {
            List<Taken> taken = new ArrayList<>();
            for (int at = 0; at < arms.size(); at++) {
                Part part = partOf(arms.get(at));
                if (part == null) {
                    return null;
                }
                taken.add(new Taken(part, where.get(at)));
            }
            return new Chosen(taken);
        }

        /** What {@code condition} states of a whole-number path of the element against a number
         *  written out, as it holds; null where it states nothing of one, or nothing says which
         *  place of the element a path reads. */
        private Narrowed narrowedBy(Core condition) {
            if (newtypes == null || !(Core.withoutStanding(condition) instanceof Core.Binary binary)
                    || !(Comparison.of(binary).orElse(null) instanceof Comparison read)) {
                return null;
            }
            Rel rel = read.claim().statedRelation();
            BigDecimal right = writtenOut(read.right());
            if (right != null && aWholeNumberPath(read.left())) {
                return narrowed(read.left(), rel, right);
            }
            BigDecimal left = writtenOut(read.left());
            if (left != null && aWholeNumberPath(read.right())) {
                return narrowed(read.right(), rel.turned(), left);
            }
            return null;
        }

        /** That {@code path} stands in {@code rel} to {@code number}, a path being the same place
         *  where {@link ElementProjection#read} reads both the same. */
        private Narrowed narrowed(Core path, Rel rel, BigDecimal number) {
            ElementProjection place = ElementProjection.read(path, element, paths, newtypes);
            return place == null ? null : new Narrowed(path, other -> place.equals(
                    ElementProjection.read(other, element, paths, newtypes)), rel,
                    ExactRatio.of(number));
        }

        private boolean aWholeNumberPath(Core e) {
            return Core.withoutStanding(e).type() == Type.INT && isAPathInside(e);
        }

        /**
         * Whether the name {@code let} gives is read here: its value is a path of the element,
         * which a read of the name stands for, or what it works out is held as given. The answer
         * so far is given to no name.
         */
        private boolean given(Core.LetIn let) {
            BindingId name = let.binder() == null ? null : let.binder().binding();
            if (name == null || name.equals(carried) || name.equals(element)) {
                return false;
            }
            if (isAPathInside(Core.withoutStanding(let.value()))) {
                paths.put(name, let.value());
                return true;
            }
            Part value = partOf(let.value());
            if (value == null || readsTheAnswerSoFar(value)) {
                return false;
            }
            bound.add(new Bound(name, value));
            return true;
        }

        private boolean isGiven(BindingId name) {
            return bound.stream().anyMatch(each -> each.name().equals(name));
        }

        /** The number {@code e} writes out, at the scale it is written, or null where it is no
         *  number written out. */
        private static BigDecimal writtenOut(Core e) {
            return switch (Core.withoutStanding(e)) {
                case Core.Int written -> BigDecimal.valueOf(written.value());
                case Core.Decimal written -> written.value();
                default -> null;
            };
        }

        /** Whether {@code e} is the element, or fields of it one inside another, or of a name
         *  given a path of it. */
        private boolean isAPathInside(Core e) {
            Core here = Core.withoutStanding(e);
            while (true) {
                switch (here) {
                    case Core.Read read -> {
                        if (element.equals(read.binding())
                                || (position != null && position.equals(read.binding()))) {
                            return true;
                        }
                        Core path = read.binding() == null ? null : paths.get(read.binding());
                        if (path == null) {
                            return false;
                        }
                        here = Core.withoutStanding(path);
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
}
