package souther.compiler.check;

import souther.compiler.abort.GetsPast;
import souther.compiler.abort.ScaleLaw;
import souther.compiler.core.Core;
import souther.compiler.inputs.DecimalOperation;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.PieceOfAnElement;
import souther.compiler.semantics.WhereAnOperatorAnswers;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.values.TextExtents;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.OptionalLong;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * Whether an operator that answers where the collection it answers fits
 * ({@link GetsPast.WhereTheAnswerFits}) answers on a run of a witness: one whose input
 * collections hold no more than its caller says they do.
 *
 * <p>How many elements each collection the run holds on the way to the operator holds at most,
 * read off the tree it stands in, given that bound for the collections of the input. Which bound
 * that is, and that a witness holding so few is one at all, is the caller's: this only says what
 * follows from it, and says nothing where it does not follow.
 *
 * <p>Each bound is read off the owner of how the collection is built, and nothing is enumerated
 * here. A collection written out holds as many as are written. One an operator answers where it
 * fits holds what its owner says it does ({@link WhatARunMayEndFor#completionApartFromTheClosuresWrittenAtIt}).
 * One assembled of at most one element for each element of another holds no more than that one
 * ({@link BoundOperationFacts#assembles}). One of which the library states how many it holds, in
 * terms of collections it is handed, holds no more than that comes to, read with the most each of
 * them holds ({@link BoundOperationFacts#settled}).
 *
 * <p>And what a walk carries, by induction on the elements it walks: where the step answers what
 * it carries with no more than some number of elements put in, of what else it is handed, what it
 * carries after every element holds no more than the seed and that number for each element
 * walked. That is a bound on every value it carries, and not only on the last, which is what an
 * operator inside the step is asked under. A step that answers anything else — what it carries
 * twice over, or something made of it — gives no such number, and nothing is said of the walk.
 *
 * <p>Counted in {@link BigInteger}, since a product of bounds can pass any machine number and a
 * wrapped one would read as small.
 */
public final class ContainerSizesUnderAWitness {

    private final Function<Core, Optional<BigInteger>> ofTheInput;
    private final Function<Core, Optional<BigInteger>> ofEachElementOfTheInput;
    private final Map<BindingId, Core> boundTo = new HashMap<>();
    private final Map<Core, WalkAt> walks = new IdentityHashMap<>();
    private final Map<BindingId, WalkAt> carriedBy = new HashMap<>();
    /** For each name asked of, whether what each bound name stands for reads it. */
    private final Map<BindingId, Map<BindingId, Boolean>> readsAsked = new HashMap<>();
    private final Set<Core> asking = new HashSet<>();
    private final Predicate<Core> aDecimalOfTheRow;
    /** The scale each name of a walk's answer so far is taken to be at while its step is read. */
    private final Map<BindingId, Long> assumedScale = new HashMap<>();

    private ContainerSizesUnderAWitness(Core within,
                                        Function<Core, Optional<BigInteger>> ofTheInput,
                                        Function<Core, Optional<BigInteger>> ofEachElement,
                                        Predicate<Core> aDecimalOfTheRow) {
        this.ofTheInput = ofTheInput;
        this.ofEachElementOfTheInput = ofEachElement;
        this.aDecimalOfTheRow = aDecimalOfTheRow;
        List<Core> calls = new ArrayList<>();
        names(within, calls);
        for (Core each : calls) {
            WalkAt walk = WalkAt.of(each, ContainerSizesUnderAWitness::blockOf);
            if (walk != null) {
                walks.put(each, walk);
                carriedBy.put(walk.carried(), walk);
            }
        }
    }

    /**
     * The most the collection {@code collection} holds on every run whose input collections hold
     * no more than {@code ofTheInput} says, read off how it is built: a collection written out,
     * one an arm of a match or a branch of a fork chooses, one assembled of what is written, and
     * a filter of a collection of the input, which holds no more than that one does.
     *
     * @param ofTheInput the most a collection of the input read at a node holds on such a run, or
     *                   nothing where the node reads no collection of the input or nothing bounds
     *                   it
     */
    public static Optional<BigInteger> mostHeld(Core collection,
                                                Function<Core, Optional<BigInteger>> ofTheInput) {
        return new ContainerSizesUnderAWitness(collection, ofTheInput, node -> Optional.empty(),
                node -> false).most(collection);
    }

    /**
     * Whether {@code operator}, standing in {@code within} and answering where {@code fits} says,
     * answers on every run whose input collections hold no more than {@code ofTheInput} says.
     *
     * @param ofTheInput    the most a collection of the input read at a node holds on such a run,
     *                      or nothing where the node reads no collection of the input or nothing
     *                      bounds it
     * @param ofEachElement the same, of the most each element of such a collection holds
     * @param aDecimalOfTheRow whether a node is a place of the input that holds a decimal as a row
     *                      is built with it ({@link DecimalOperation#writtenForARow}), written at no
     *                      more places than a row is built at
     */
    public static boolean answersOn(Core within, Core operator, GetsPast completion,
                                    Function<Core, Optional<BigInteger>> ofTheInput,
                                    Function<Core, Optional<BigInteger>> ofEachElement,
                                    Predicate<Core> aDecimalOfTheRow) {
        return new ContainerSizesUnderAWitness(within, ofTheInput, ofEachElement, aDecimalOfTheRow)
                .answers(operator, completion);
    }

    /** Whether {@code operator}, standing in what this reads and answering where
     *  {@code completion} says, answers on every run this reads. */
    private boolean answers(Core operator, GetsPast completion) {
        return switch (completion) {
            case GetsPast.Always _ -> true;
            case GetsPast.WhereTheAnswerFits(LinearForm<LawNumber<Integer>> answer) ->
                    answer(operator, answer)
                            .map(most -> most.compareTo(GetsPast.MOST_ELEMENTS) <= 0)
                            .orElse(false);
            // A total of no {@code Int} or of one is nought or that one, which is an {@code Int};
            // of two or more it turns on the values, which are read only where they are written
            // out, and added up exactly.
            case GetsPast.WhereTheTotalFits(int at) -> {
                List<Core> operands = operandsOf(operator);
                if (operands == null || at >= operands.size()) {
                    yield false;
                }
                Optional<BigInteger> written = writtenTotal(operands.get(at));
                yield written.isPresent()
                        ? anIntSumAnswersAt(written.get())
                        : most(operands.get(at))
                                .map(most -> most.compareTo(BigInteger.ONE) <= 0).orElse(false);
            }
            // How long a text a conversion makes turns on the text, and what a run holds of
            // collections says nothing of it.
            case GetsPast.WhereTheTextFits _ -> false;
            // Whether the scales leave room is read off what each operand is, by the rule the
            // operations a row is asked of are ({@link DecimalOperation#hasRoomAt}).
            case GetsPast.WhereTheScalesHaveRoom(ScaleLaw law) -> {
                List<Core> args = operandsOf(operator);
                OptionalLong first = args == null ? OptionalLong.empty() : scaleHandedAt(law, args,
                        law.firstAt());
                OptionalLong second = args == null ? OptionalLong.empty() : scaleHandedAt(law, args,
                        law.secondAt());
                yield first.isPresent() && second.isPresent()
                        && DecimalOperation.hasRoomAt(law, first.getAsLong(), second.getAsLong());
            }
            case GetsPast.NotKnown _ -> false;
        };
    }

    /**
     * The scale furthest from nought that the decimal {@code e} comes to is written at on a run of
     * a row, or nothing where it is not read here: a decimal written out is at its own scale, a
     * place of the row at no more than a row is built at, and a sum, a difference or a product of
     * those as {@link DecimalOperation#scaleOfTheAnswer} says. A name is what it is bound to, and
     * the answer so far of a walk is at the scale the seed is at or that the step keeps it at.
     */
    private OptionalLong scaleOf(Core e) {
        Core node = Core.withoutStanding(e);
        switch (node) {
            case Core.Decimal written -> {
                return OptionalLong.of(Math.abs((long) written.value().scale()));
            }
            case Core.Read name -> {
                Long assumed = assumedScale.get(name.binding());
                if (assumed != null) {
                    return OptionalLong.of(assumed);
                }
                WalkAt walk = carriedBy.get(name.binding());
                if (walk != null) {
                    return scaleCarried(walk);
                }
                Core value = boundTo.get(name.binding());
                if (value != null) {
                    return asking.add(value) ? scaleOfWhileAsking(value) : OptionalLong.empty();
                }
            }
            case Core.LetIn li -> {
                return scaleOf(li.body());
            }
            // Negating a number leaves it the places it had.
            case Core.Neg negated -> {
                return scaleOf(negated.operand());
            }
            case Core.If fork -> {
                return larger(scaleOf(fork.then()), scaleOf(fork.els()));
            }
            default -> {
                // A sum, a difference or a product, in whatever shape the tree gives it: its
                // owner says it is one.
                List<Core> operands = operandsOf(node);
                if (operands != null && WhatARunMayEndFor
                        .completionApartFromTheClosuresWrittenAtIt(node)
                        instanceof GetsPast.WhereTheScalesHaveRoom(ScaleLaw law)) {
                    return scaleOfTheAnswer(law, operands);
                }
                AnOperationApplied applied = AnOperationApplied.of(node);
                List<Integer> made = applied == null ? null : DefaultBoundOperationFacts.get()
                        .argumentsAnAnswerIsMadeOf(applied.operation());
                if (made != null) {
                    return scaleOfWhatIsMadeOf(applied.args(), made);
                }
            }
        }
        return aDecimalOfTheRow.test(node)
                ? OptionalLong.of(DecimalOperation.PLACES_A_ROW_IS_BUILT_AT) : OptionalLong.empty();
    }

    private OptionalLong scaleOfWhileAsking(Core value) {
        try {
            return scaleOf(value);
        } finally {
            asking.remove(value);
        }
    }

    /**
     * The scale of an answer made of the arguments at {@code made}: that of the one with the most,
     * a whole number having none. Nothing where an argument is neither.
     */
    private OptionalLong scaleOfWhatIsMadeOf(List<Core> args, List<Integer> made) {
        OptionalLong most = OptionalLong.of(0);
        for (int at : made) {
            Core argument = args.get(at);
            OptionalLong scale = Type.INT.equals(argument.type()) ? OptionalLong.of(0)
                    : Type.DECIMAL.equals(argument.type()) ? scaleOf(argument)
                    : OptionalLong.empty();
            if (scale.isEmpty()) {
                return OptionalLong.empty();
            }
            most = OptionalLong.of(Math.max(most.getAsLong(), scale.getAsLong()));
        }
        return most;
    }

    private OptionalLong scaleOfTheAnswer(ScaleLaw law, List<Core> args) {
        OptionalLong first = scaleHandedAt(law, args, law.firstAt());
        OptionalLong second = scaleHandedAt(law, args, law.secondAt());
        return first.isPresent() && second.isPresent()
                ? OptionalLong.of(DecimalOperation.scaleOfTheAnswer(law, first.getAsLong(),
                        second.getAsLong()))
                : OptionalLong.empty();
    }

    /**
     * The scale of the argument {@code at} an operation under {@code law} is handed: what the
     * argument is, where it is a number it works on, and the whole number it is written as, where
     * it is the scale asked for.
     */
    private OptionalLong scaleHandedAt(ScaleLaw law, List<Core> args, int at) {
        if (at >= args.size()) {
            return OptionalLong.empty();
        }
        if (law instanceof ScaleLaw.Asked asked && at == asked.scaleAt()) {
            Optional<BigInteger> written = writtenWhole(args.get(at));
            return written.isPresent() && written.get().bitLength() < Integer.SIZE
                    ? OptionalLong.of(written.get().abs().longValueExact()) : OptionalLong.empty();
        }
        return scaleOf(args.get(at));
    }

    /**
     * The scale every answer so far of {@code walk} is at, by induction on the elements: at the
     * seed's, and where the step answers no further from nought than the scale it is handed, at
     * that. Where the step goes further from it — a product, which adds a scale at every element
     * — no scale holds on every step, and nothing is said.
     */
    private OptionalLong scaleCarried(WalkAt walk) {
        BindingId carried = walk.carried();
        if (!asking.add(walk.step())) {
            return OptionalLong.empty();
        }
        try {
            OptionalLong seed = scaleOf(walk.seed());
            if (seed.isEmpty()) {
                return OptionalLong.empty();
            }
            long held = seed.getAsLong();
            for (int round = 0; round < 2; round++) {
                assumedScale.put(carried, held);
                OptionalLong step = scaleOf(walk.step().body());
                if (step.isEmpty()) {
                    return OptionalLong.empty();
                }
                if (step.getAsLong() <= held) {
                    return OptionalLong.of(held);
                }
                held = step.getAsLong();
            }
            return OptionalLong.empty();
        } finally {
            assumedScale.remove(carried);
            asking.remove(walk.step());
        }
    }

    private static OptionalLong larger(OptionalLong one, OptionalLong other) {
        return one.isPresent() && other.isPresent()
                ? OptionalLong.of(Math.max(one.getAsLong(), other.getAsLong()))
                : OptionalLong.empty();
    }

    /** Whether an {@code Int} sum coming to {@code total} answers it, as the language says
     *  ({@link WhereAnOperatorAnswers}). */
    private static boolean anIntSumAnswersAt(BigInteger total) {
        return WhereAnOperatorAnswers.ofATotal(Type.INT)
                instanceof WhereAnOperatorAnswers.WhereItsExactValueIsHeld(
                        BigInteger least, BigInteger greatest)
                && total.compareTo(least) >= 0 && total.compareTo(greatest) <= 0;
    }

    /** The exact total of {@code list} where it is written out of whole numbers written out, or
     *  nothing where it is not. */
    private static Optional<BigInteger> writtenTotal(Core list) {
        if (!(Core.withoutStanding(list) instanceof Core.ListLit written)) {
            return Optional.empty();
        }
        BigInteger total = BigInteger.ZERO;
        for (Core each : written.elements()) {
            Optional<BigInteger> number = writtenWhole(each);
            if (number.isEmpty()) {
                return Optional.empty();
            }
            total = total.add(number.get());
        }
        return Optional.of(total);
    }

    /** {@code e} where it is a whole number written out, or one negated. */
    private static Optional<BigInteger> writtenWhole(Core e) {
        return switch (Core.withoutStanding(e)) {
            case Core.Int number -> Optional.of(BigInteger.valueOf(number.value()));
            case Core.Neg negated -> writtenWhole(negated.operand()).map(BigInteger::negate);
            default -> Optional.empty();
        };
    }

    /** What {@code node} is handed, in the order it is written, or null where it applies
     *  nothing. */
    private static List<Core> operandsOf(Core node) {
        AnOperationApplied applied = AnOperationApplied.of(node);
        return applied != null ? applied.args()
                : Core.withoutStanding(node) instanceof Core.Binary binary
                        ? List.of(binary.left(), binary.right()) : null;
    }

    /** Every name {@code e} binds to a value, and every operation applied in it, into
     *  {@code calls}: the walks among them. */
    private void names(Core e, List<Core> calls) {
        Core node = Core.withoutStanding(e);
        if (node instanceof Core.LetIn li && li.binder() != null) {
            boundTo.put(li.binder().binding(), li.value());
        } else if (AnOperationApplied.of(node) != null) {
            calls.add(node);
        }
        Core.forEachChild(node, child -> names(child, calls));
    }

    /**
     * The block {@code closure} handed to a walk is, where the walk alone applies it: written at
     * the walk. A step applied anywhere besides is handed there what that application hands it,
     * and what it carries is no longer what the walk carries. A step the source hands by name
     * reaches the tree read here written at the walk, as a closure applying it. Null where it is
     * no block written there.
     */
    private static Core.Block blockOf(Core closure) {
        return Core.withoutStanding(closure) instanceof Core.Block written ? written : null;
    }

    /** The most the answer of {@code node} holds, as {@code size}, a number of what it is handed
     *  by place, says. */
    private Optional<BigInteger> answer(Core node, LinearForm<LawNumber<Integer>> size) {
        List<Core> operands = operandsOf(node);
        if (operands == null) {
            return Optional.empty();
        }
        return mostOf(size, at -> at < operands.size() ? operands.get(at) : null);
    }

    /** The most the collection {@code e} answers holds on such a run, or nothing where that is
     *  not read here. */
    private Optional<BigInteger> most(Core e) {
        Core node = Core.withoutStanding(e);
        Optional<BigInteger> input = ofTheInput.apply(node);
        if (input.isPresent()) {
            return input;
        }
        if (!asking.add(node)) {
            return Optional.empty();
        }
        try {
            return mostOf(node);
        } finally {
            asking.remove(node);
        }
    }

    private Optional<BigInteger> mostOf(Core node) {
        return switch (Core.withoutStanding(node)) {
            case Core.ListLit written -> Optional.of(BigInteger.valueOf(written.elements().size()));
            case Core.Read name -> {
                WalkAt walk = carriedBy.get(name.binding());
                if (walk != null) {
                    yield carried(walk, true);
                }
                Core value = boundTo.get(name.binding());
                yield value == null ? Optional.empty() : most(value);
            }
            case Core.LetIn li -> most(li.body());
            case Core.If fork -> larger(most(fork.then()), most(fork.els()));
            // A part of what a walk carries that is a walk of its own, at a step or of what the
            // walk answers.
            case Core.TupleGet _, Core.FieldAccess _, Core.FieldProjection _
                    when aPartOfAWalk(SeededWalk.Part.taken(node)) instanceof PartOfAWalk(
                            WalkAt walk, boolean handedToTheStep) ->
                    carried(walk, handedToTheStep);
            // Of the value an attempt answers where it is built or where it is refused: how many
            // elements it holds if it answers, not that it does.
            case Core.IfConstructed attempt -> {
                Optional<BigInteger> out = most(attempt.then());
                for (Core.ElseArm arm : attempt.els()) {
                    out = larger(out, most(arm.body()));
                }
                yield out;
            }
            case Core.Match match -> {
                Optional<BigInteger> out = Optional.of(BigInteger.ZERO);
                for (Core.Case arm : match.cases()) {
                    out = larger(out, most(arm.body()));
                }
                yield out;
            }
            default -> {
                WalkAt walk = walks.get(node);
                if (walk != null) {
                    yield carried(walk, false);
                }
                if (WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(node)
                        instanceof GetsPast.WhereTheAnswerFits(
                                LinearForm<LawNumber<Integer>> size)) {
                    yield answer(node, size);
                }
                yield assembledOrStated(node);
            }
        };
    }

    /**
     * The most what {@code node} answers holds where the library says how many: a collection
     * assembled of at most one element for each element of another, or one of which a law of how
     * many it holds is stated over collections it is handed.
     */
    private Optional<BigInteger> assembledOrStated(Core node) {
        AnOperationApplied applied = AnOperationApplied.of(node);
        if (applied == null) {
            return Optional.empty();
        }
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        BoundOperationFacts.Assembled assembled = facts.assembles(applied.operation());
        if (assembled != null && assembled.piece() != PieceOfAnElement.WHAT_THE_CLOSURE_ANSWERS) {
            Core source = applied.argument(assembled.source());
            return source == null ? Optional.empty() : most(source);
        }
        // Built from the elements of one container, and no more of them than it holds.
        BuiltFrom<DeclaredArgument> built = facts.buildsItsResultFrom(applied.operation());
        if (built != null && built.outputs().size() == 1 && built.lineage().source() != null) {
            Core source = applied.argument(built.lineage().source().argument());
            if (source != null) {
                return most(source);
            }
        }
        if (facts.settled(applied.operation(), OperationLaw.Observed.SIZE)
                instanceof BoundOperationFacts.Settled.ByALaw(
                        OperationLaw.Size<DeclaredArgument> law, var _)) {
            Optional<BigInteger> out = Optional.of(BigInteger.ZERO);
            for (OperationLaw.Size.Case<DeclaredArgument> each : law.cases()) {
                out = larger(out, mostOf(each.equalTo(), applied));
            }
            return out;
        }
        // The pieces of a string are one more than the separators it holds, and a string holds
        // no more code points than a String can.
        if (facts.piecesOf(applied.operation()) != null) {
            return Optional.of(BigInteger.valueOf(TextExtents.LONGEST_STRING).add(BigInteger.ONE));
        }
        return Optional.empty();
    }

    /** The same, of {@code form} over the arguments of {@code applied}. */
    private Optional<BigInteger> mostOf(LinearForm<LawNumber<DeclaredArgument>> form,
                                        AnOperationApplied applied) {
        return mostOf(form, applied::argument);
    }

    /**
     * The most {@code form}, a number of what a site is handed, comes to: each number in it the
     * most a collection {@code handed} names holds, or a part of one, or the most the elements of
     * one hold between them — as many as it holds, each holding as many as one of them may, or
     * as many as the closure handed beside it answers on one.
     */
    private <A> Optional<BigInteger> mostOf(LinearForm<LawNumber<A>> form,
                                            Function<A, Core> handed) {
        Optional<BigInteger> out = whole(form.constant());
        for (Map.Entry<LawNumber<A>, ExactRatio> term : form.coefs().entrySet()) {
            if (out.isEmpty() || term.getValue().signum() < 0) {
                return Optional.empty();
            }
            Optional<BigInteger> held = switch (term.getKey()) {
                case LawNumber.SizeOf<A>(LawSubject.Argument<A>(A argument)) -> mostIn(handed,
                        argument);
                case LawNumber.HowManyMeet<A>(A argument, var _) -> mostIn(handed, argument);
                case LawNumber.HowManyDifferent<A>(A argument, var _) -> mostIn(handed, argument);
                case LawNumber.SumOver<A>(A argument, LawNumber.SizeOf<A>(
                        LawSubject.ElementOf<A>(A same))) when same.equals(argument) -> {
                    Core container = handed.apply(argument);
                    yield container == null ? Optional.empty()
                            : times(most(container), mostOfAnElement(container));
                }
                case LawNumber.SumOver<A>(A argument, LawNumber.SizeOf<A>(
                        LawSubject.WhatTheClosureAnswers<A>(A closure))) -> {
                    Core container = handed.apply(argument);
                    Core function = handed.apply(closure);
                    yield container == null || function == null
                            || !(Core.withoutStanding(function) instanceof Core.Block made)
                            ? Optional.empty() : times(most(container), most(made.body()));
                }
                default -> Optional.empty();
            };
            Optional<BigInteger> coefficient = whole(term.getValue());
            if (held.isEmpty() || coefficient.isEmpty()) {
                return Optional.empty();
            }
            out = Optional.of(out.get().add(coefficient.get().multiply(held.get())));
        }
        return out;
    }

    /** The most the collection {@code handed} names at {@code argument} holds. */
    private <A> Optional<BigInteger> mostIn(Function<A, Core> handed, A argument) {
        Core container = handed.apply(argument);
        return container == null ? Optional.empty() : most(container);
    }

    /** The most any element of the collection {@code container} holds: of one written out, the
     *  most of those written; of one of the input, as the caller says. */
    private Optional<BigInteger> mostOfAnElement(Core container) {
        Core node = Core.withoutStanding(container);
        Optional<BigInteger> input = ofEachElementOfTheInput.apply(node);
        if (input.isPresent()) {
            return input;
        }
        if (!(node instanceof Core.ListLit written)) {
            return Optional.empty();
        }
        Optional<BigInteger> out = Optional.of(BigInteger.ZERO);
        for (Core each : written.elements()) {
            out = larger(out, most(each));
        }
        return out;
    }

    private static Optional<BigInteger> times(Optional<BigInteger> one,
                                              Optional<BigInteger> other) {
        return one.isPresent() && other.isPresent()
                ? Optional.of(one.get().multiply(other.get())) : Optional.empty();
    }

    /** {@code ratio} rounded up to a whole number, or nothing where it is below nought. */
    private static Optional<BigInteger> whole(ExactRatio ratio) {
        return ratio.signum() >= 0 && ratio.ceiling() instanceof ExactAnswer.Held<BigInteger>(var up)
                ? Optional.of(up) : Optional.empty();
    }

    /**
     * The walk of a part of what a walk carries, and whether it is read where its step is handed
     * that ({@link #carried}).
     */
    private record PartOfAWalk(WalkAt walk, boolean handedToTheStep) {}

    /**
     * The walk of the part {@code taken} takes, where it takes it of what a walk carries — read
     * through the names given that on the way, {@code let (n, ys) = acc} among them — or of what
     * a walk answers, and that part is a walk of its own ({@link WalkAt#ofThePart}). Null where it
     * is none of these.
     */
    private PartOfAWalk aPartOfAWalk(SeededWalk.Taken taken) {
        Core whole = Core.withoutStanding(taken.whole());
        Set<BindingId> followed = new HashSet<>();
        while (whole instanceof Core.Read name && carriedBy.get(name.binding()) == null
                && boundTo.get(name.binding()) != null && followed.add(name.binding())) {
            whole = Core.withoutStanding(boundTo.get(name.binding()));
        }
        WalkAt walking = whole instanceof Core.Read name ? carriedBy.get(name.binding()) : null;
        boolean handed = walking != null;
        WalkAt walk = handed ? walking : walks.get(whole);
        // A part of a part is a part of the walk of the outer one.
        if (walk == null && SeededWalk.Part.taken(whole) instanceof SeededWalk.Taken inner
                && aPartOfAWalk(inner) instanceof PartOfAWalk outer) {
            walk = outer.walk();
            handed = outer.handedToTheStep();
        }
        WalkAt part = walk == null ? null : walk.ofThePart(taken);
        return part == null ? null : new PartOfAWalk(part, handed);
    }

    /**
     * The most what {@code walk} carries holds, by induction on the elements it walks: the seed,
     * and for each element the most the step puts in beside what it carries. After every element
     * where {@code handedToTheStep} is false, which is what the walk answers; and before the step
     * is applied to an element where it is true, which is one element fewer — what the step is
     * handed at the last element is what it carried after the one before.
     */
    private Optional<BigInteger> carried(WalkAt walk, boolean handedToTheStep) {
        Optional<BigInteger> seed = most(walk.seed());
        BigInteger elements = walked(walk.container());
        Optional<BigInteger> each = putIn(walk.step().body(), walk.carried());
        if (seed.isEmpty() || each.isEmpty()) {
            return Optional.empty();
        }
        BigInteger steps = handedToTheStep
                ? elements.subtract(BigInteger.ONE).max(BigInteger.ZERO) : elements;
        return Optional.of(seed.get().add(steps.multiply(each.get())));
    }

    /**
     * How many elements {@code container}, what a walk walks, hands the step at most: what is read
     * of it, and no more than a collection holds ({@link GetsPast#MOST_ELEMENTS}) whatever is
     * read, since a string holds fewer code points than that. It is there before the walk begins,
     * and a run that would make one holding more stops where it makes it, which that operator's
     * own completion says. Of what is walked alone: what a walk builds is read by what it carries.
     */
    private BigInteger walked(Core container) {
        return most(container).map(most -> most.min(GetsPast.MOST_ELEMENTS))
                .orElse(GetsPast.MOST_ELEMENTS);
    }

    /**
     * The most {@code body} puts in beside what is carried under {@code carried}, where it answers
     * that with elements put in: nought where it answers it as it is, and the most what an operator
     * answering where the collection fits puts beside it, of what else it is handed. Nothing where
     * it answers anything else.
     *
     * <p>A choice reading what is carried chooses by it, and what each arm puts in is then not
     * what the choice puts in on every run — but for a lookup of a key in it, which reads a value
     * filed under that key and puts in nothing: each arm puts in what it puts beside the same
     * collection, whichever is taken.
     *
     * <p>What is carried is read under any name given it ({@link #isCarried}): a step handed by
     * name is applied as a closure that gives its parameters the names the step was written with.
     */
    private Optional<BigInteger> putIn(Core body, BindingId carried) {
        Core node = Core.withoutStanding(body);
        if (isCarried(node, carried)) {
            return Optional.of(BigInteger.ZERO);
        }
        return switch (node) {
            case Core.If fork -> reads(fork.cond(), carried) ? Optional.empty()
                    : larger(putIn(fork.then(), carried), putIn(fork.els(), carried));
            case Core.Match match -> {
                if (reads(match.scrutinee(), carried)
                        && !isALookupIn(match.scrutinee(), carried)) {
                    yield Optional.empty();
                }
                Optional<BigInteger> out = Optional.of(BigInteger.ZERO);
                for (Core.Case arm : match.cases()) {
                    out = larger(out, putIn(arm.body(), carried));
                }
                yield out;
            }
            case Core.LetIn li -> reads(li.value(), carried) && !isCarried(li.value(), carried)
                    ? Optional.empty() : putIn(li.body(), carried);
            default -> putInByAnOperator(node, carried);
        };
    }

    /**
     * The most an operator answering where the collection fits, {@code node}, puts in beside
     * what is carried under {@code carried} where it is handed that as one of the operands it
     * counts, of the others ({@link #putIn}).
     */
    private Optional<BigInteger> putInByAnOperator(Core node, BindingId carried) {
        if (!(WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(node)
                instanceof GetsPast.WhereTheAnswerFits(LinearForm<LawNumber<Integer>> size))) {
            return Optional.empty();
        }
        AnOperationApplied applied = AnOperationApplied.of(node);
        if (applied == null) {
            return Optional.empty();
        }
        List<Core> operands = applied.args();
        // What is carried, under any name given it, counted once and as it is; every other
        // operand reads none of it.
        Integer carriedAt = null;
        for (int at = 0; at < operands.size(); at++) {
            Core operand = Core.withoutStanding(operands.get(at));
            LawNumber<Integer> itsSize = new LawNumber.SizeOf<>(new LawSubject.Argument<>(at));
            if (carriedAt == null && isCarried(operand, carried)
                    && ExactRatio.ONE.equals(size.coefs().get(itsSize))) {
                carriedAt = at;
            } else if (reads(operand, carried)) {
                return Optional.empty();
            }
        }
        if (carriedAt == null) {
            return Optional.empty();
        }
        LinearForm<LawNumber<Integer>> beside = size.minus(LinearForm.atom(
                new LawNumber.SizeOf<>(new LawSubject.Argument<>(carriedAt)))).orNull();
        return beside == null ? Optional.empty()
                : mostOf(beside, at -> at < operands.size() ? operands.get(at) : null);
    }

    /** Whether {@code e} looks a key up in what is carried under {@code carried}, with a key
     *  that does not read it ({@link KeyedAccumulation#mapLookedUpIn}). */
    private boolean isALookupIn(Core e, BindingId carried) {
        AnOperationApplied applied = AnOperationApplied.of(e);
        Core map = applied == null ? null : KeyedAccumulation.mapLookedUpIn(applied);
        if (map == null || !isCarried(map, carried)) {
            return false;
        }
        for (Core each : applied.args()) {
            if (each != map && reads(each, carried)) {
                return false;
            }
        }
        return true;
    }

    /** Whether {@code e} is what is carried under {@code carried}: that name, or a name bound
     *  to it. */
    private boolean isCarried(Core e, BindingId carried) {
        return Core.withoutStanding(e) instanceof Core.Read name
                && (name.binding().equals(carried)
                        || (boundTo.get(name.binding()) instanceof Core value
                                && isCarried(value, carried)));
    }

    /** Whether {@code e} reads {@code name} anywhere, under that name or a name bound to what
     *  reads it: of each name bound, asked once, since a name is read wherever it is in scope. */
    private boolean reads(Core e, BindingId name) {
        Core node = Core.withoutStanding(e);
        if (node instanceof Core.Read read) {
            if (read.binding().equals(name)) {
                return true;
            }
            Core value = boundTo.get(read.binding());
            if (value == null) {
                return false;
            }
            Map<BindingId, Boolean> asked = readsAsked.computeIfAbsent(name, k -> new HashMap<>());
            Boolean known = asked.get(read.binding());
            if (known == null) {
                known = reads(value, name);
                asked.put(read.binding(), known);
            }
            return known;
        }
        boolean[] found = {false};
        Core.forEachChild(node, child -> found[0] |= reads(child, name));
        return found[0];
    }

    private static Optional<BigInteger> larger(Optional<BigInteger> one,
                                               Optional<BigInteger> other) {
        return one.isPresent() && other.isPresent()
                ? Optional.of(one.get().max(other.get())) : Optional.empty();
    }

    /**
     * A walk of the library applied: what it starts from, the collection it walks, its step, and
     * the name the step is handed what it carries under ({@link Reductions},
     * {@link Combinators}).
     */
    private record WalkAt(Core seed, Core container, Core.Block step, Core.Binder accumulator) {

        BindingId carried() {
            return accumulator.binding();
        }

        /** This walk read for the part {@code part} takes of what it carries alone
         *  ({@link SeededWalk#ofThePart}), or null where that part is no walk of its own. */
        WalkAt ofThePart(SeededWalk.Taken part) {
            SeededWalk.OfThePart alone = SeededWalk.ofThePart(seed, step, accumulator, part);
            return alone == null ? null
                    : new WalkAt(alone.seed(), container, alone.step(), accumulator);
        }

        /** {@code e} as a walk, or null where it applies none, or its step is no block
         *  {@code blockOf} reaches. */
        static WalkAt of(Core e, Function<Core, Core.Block> blockOf) {
            AnOperationApplied applied = AnOperationApplied.of(e);
            Reductions.Reducing walk = applied == null ? null
                    : Reductions.reducing(applied.operation(), applied.args(), blockOf);
            return walk == null || walk.accumulator().binding() == null ? null
                    : new WalkAt(walk.seed(), walk.container(), walk.step(), walk.accumulator());
        }
    }
}
