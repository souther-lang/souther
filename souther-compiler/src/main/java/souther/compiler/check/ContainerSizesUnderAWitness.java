package souther.compiler.check;

import souther.compiler.abort.GetsPast;
import souther.compiler.core.Core;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.Combinator;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.PieceOfAnElement;
import souther.compiler.semantics.WhereAnOperatorAnswers;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;

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
    private final Map<BindingId, Core> boundTo = new HashMap<>();
    private final Map<BindingId, Core> carriedBy = new HashMap<>();
    private final Set<Core> asking = new HashSet<>();

    private ContainerSizesUnderAWitness(Core within,
                                        Function<Core, Optional<BigInteger>> ofTheInput) {
        this.ofTheInput = ofTheInput;
        names(within);
    }

    /**
     * Whether {@code operator}, standing in {@code within} and answering where {@code fits} says,
     * answers on every run whose input collections hold no more than {@code ofTheInput} says.
     *
     * @param ofTheInput the most a collection of the input read at a node holds on such a run, or
     *                   nothing where the node reads no collection of the input or nothing bounds
     *                   it
     */
    public static boolean answersOn(Core within, Core operator, GetsPast completion,
                                    Function<Core, Optional<BigInteger>> ofTheInput) {
        ContainerSizesUnderAWitness reading = new ContainerSizesUnderAWitness(within, ofTheInput);
        return switch (completion) {
            case GetsPast.Always _ -> true;
            case GetsPast.WhereTheAnswerFits(GetsPast.AnswerSize answer) ->
                    reading.answer(operator, answer)
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
                        : reading.most(operands.get(at))
                                .map(most -> most.compareTo(BigInteger.ONE) <= 0).orElse(false);
            }
            case GetsPast.NotKnown _ -> false;
        };
    }

    /** Whether an {@code Int} sum coming to {@code total} answers it, as the language says
     *  ({@link WhereAnOperatorAnswers}). */
    private static boolean anIntSumAnswersAt(BigInteger total) {
        return WhereAnOperatorAnswers.ofAnOperator(BinOp.ADD, Type.INT,
                List.of(Type.INT, Type.INT))
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

    /** Every name {@code e} binds to a value, and every name a walk in it carries its value
     *  under, with the walk. */
    private void names(Core e) {
        Core node = Core.withoutStanding(e);
        if (node instanceof Core.LetIn li && li.binder() != null) {
            boundTo.put(li.binder().binding(), li.value());
        }
        WalkAt walk = WalkAt.of(node);
        if (walk != null) {
            carriedBy.put(walk.carried(), node);
        }
        Core.forEachChild(node, this::names);
    }

    /** The most the answer of {@code node} holds, as {@code size} says of what it is handed. */
    private Optional<BigInteger> answer(Core node, GetsPast.AnswerSize size) {
        List<Core> operands = operandsOf(node);
        if (operands == null) {
            return Optional.empty();
        }
        return switch (size) {
            case GetsPast.AnswerSize.SumOf(List<Integer> at, int more) -> {
                BigInteger total = BigInteger.valueOf(more);
                for (int each : at) {
                    Optional<BigInteger> one = each < operands.size()
                            ? most(operands.get(each)) : Optional.empty();
                    if (one.isEmpty()) {
                        yield Optional.empty();
                    }
                    total = total.add(one.get());
                }
                yield Optional.of(total);
            }
            case GetsPast.AnswerSize.PiecesOf(int source, int function) -> {
                if (source >= operands.size() || function >= operands.size()
                        || !(Core.withoutStanding(operands.get(function))
                                instanceof Core.Block made)) {
                    yield Optional.empty();
                }
                Optional<BigInteger> elements = most(operands.get(source));
                Optional<BigInteger> piece = most(made.body());
                yield elements.isPresent() && piece.isPresent()
                        ? Optional.of(elements.get().multiply(piece.get())) : Optional.empty();
            }
        };
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
                Core walk = carriedBy.get(name.binding());
                if (walk != null) {
                    yield carried(WalkAt.of(walk), true);
                }
                Core value = boundTo.get(name.binding());
                yield value == null ? Optional.empty() : most(value);
            }
            case Core.LetIn li -> most(li.body());
            case Core.If fork -> larger(most(fork.then()), most(fork.els()));
            case Core.Match match -> {
                Optional<BigInteger> out = Optional.of(BigInteger.ZERO);
                for (Core.Case arm : match.cases()) {
                    out = larger(out, most(arm.body()));
                }
                yield out;
            }
            default -> {
                WalkAt walk = WalkAt.of(node);
                if (walk != null) {
                    yield carried(walk, false);
                }
                if (WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(node)
                        instanceof GetsPast.WhereTheAnswerFits(GetsPast.AnswerSize size)) {
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
        if (facts.settled(applied.operation(), OperationLaw.Observed.SIZE)
                instanceof BoundOperationFacts.Settled.ByALaw(
                        OperationLaw.Size<DeclaredArgument> law, var _)) {
            Optional<BigInteger> out = Optional.of(BigInteger.ZERO);
            for (OperationLaw.Size.Case<DeclaredArgument> each : law.cases()) {
                out = larger(out, mostOf(each.equalTo(), applied));
            }
            return out;
        }
        return Optional.empty();
    }

    /** The most {@code form} comes to, each number in it the most a collection handed to
     *  {@code applied} holds, or a part of one. */
    private Optional<BigInteger> mostOf(LinearForm<LawNumber<DeclaredArgument>> form,
                                        AnOperationApplied applied) {
        Optional<BigInteger> out = whole(form.constant());
        for (Map.Entry<LawNumber<DeclaredArgument>, ExactRatio> term : form.coefs().entrySet()) {
            if (out.isEmpty() || term.getValue().signum() < 0) {
                return Optional.empty();
            }
            DeclaredArgument container = switch (term.getKey()) {
                case LawNumber.SizeOf<DeclaredArgument>(
                        LawSubject.Argument<DeclaredArgument>(var argument)) -> argument;
                case LawNumber.HowManyMeet<DeclaredArgument>(var argument, var _) -> argument;
                case LawNumber.HowManyDifferent<DeclaredArgument>(var argument, var _) -> argument;
                default -> null;
            };
            Core handed = container == null ? null : applied.argument(container);
            Optional<BigInteger> held = handed == null ? Optional.empty() : most(handed);
            Optional<BigInteger> coefficient = whole(term.getValue());
            if (held.isEmpty() || coefficient.isEmpty()) {
                return Optional.empty();
            }
            out = Optional.of(out.get().add(coefficient.get().multiply(held.get())));
        }
        return out;
    }

    /** {@code ratio} rounded up to a whole number, or nothing where it is below nought. */
    private static Optional<BigInteger> whole(ExactRatio ratio) {
        return ratio.signum() >= 0 && ratio.ceiling() instanceof ExactAnswer.Held<BigInteger>(var up)
                ? Optional.of(up) : Optional.empty();
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
        Optional<BigInteger> elements = most(walk.container());
        Optional<BigInteger> each = putIn(walk.step().body(), walk.carried());
        if (seed.isEmpty() || elements.isEmpty() || each.isEmpty()) {
            return Optional.empty();
        }
        BigInteger steps = handedToTheStep
                ? elements.get().subtract(BigInteger.ONE).max(BigInteger.ZERO) : elements.get();
        return Optional.of(seed.get().add(steps.multiply(each.get())));
    }

    /**
     * The most {@code body} puts in beside what is carried under {@code carried}, where it answers
     * that with elements put in: nought where it answers it as it is, and the most what an operator
     * answering where the collection fits puts beside it, of what else it is handed. Nothing where
     * it answers anything else.
     */
    private Optional<BigInteger> putIn(Core body, BindingId carried) {
        return switch (Core.withoutStanding(body)) {
            case Core.Read name when name.binding().equals(carried) ->
                    Optional.of(BigInteger.ZERO);
            case Core.If fork -> mentions(fork.cond(), carried) ? Optional.empty()
                    : larger(putIn(fork.then(), carried), putIn(fork.els(), carried));
            case Core.Match match -> {
                if (mentions(match.scrutinee(), carried)) {
                    yield Optional.empty();
                }
                Optional<BigInteger> out = Optional.of(BigInteger.ZERO);
                for (Core.Case arm : match.cases()) {
                    out = larger(out, putIn(arm.body(), carried));
                }
                yield out;
            }
            case Core.LetIn li -> mentions(li.value(), carried) ? Optional.empty()
                    : putIn(li.body(), carried);
            case Core node -> putInByAnOperator(node, carried);
        };
    }

    /**
     * The most an operator answering where the collection fits, {@code node}, puts in beside
     * what is carried under {@code carried} where it is handed that as one of the operands it
     * counts, of the others ({@link #putIn}).
     */
    private Optional<BigInteger> putInByAnOperator(Core node, BindingId carried) {
        if (!(WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(node)
                instanceof GetsPast.WhereTheAnswerFits(
                        GetsPast.AnswerSize.SumOf(List<Integer> at, int more)))) {
            return Optional.empty();
        }
        AnOperationApplied applied = AnOperationApplied.of(node);
        if (applied == null) {
            return Optional.empty();
        }
        List<Core> operands = applied.args();
        int carriedAt = -1;
        BigInteger total = BigInteger.valueOf(more);
        for (int each : at) {
            if (each >= operands.size()) {
                return Optional.empty();
            }
            Core operand = Core.withoutStanding(operands.get(each));
            if (operand instanceof Core.Read name && name.binding().equals(carried)
                    && carriedAt < 0) {
                carriedAt = each;
                continue;
            }
            if (mentions(operand, carried)) {
                return Optional.empty();
            }
            Optional<BigInteger> one = most(operand);
            if (one.isEmpty()) {
                return Optional.empty();
            }
            total = total.add(one.get());
        }
        for (int other = 0; other < operands.size(); other++) {
            if (!at.contains(other) && mentions(operands.get(other), carried)) {
                return Optional.empty();
            }
        }
        return carriedAt < 0 ? Optional.empty() : Optional.of(total);
    }

    /** Whether {@code e} reads {@code name} anywhere. */
    private static boolean mentions(Core e, BindingId name) {
        Core node = Core.withoutStanding(e);
        if (node instanceof Core.Read read && read.binding().equals(name)) {
            return true;
        }
        boolean[] found = {false};
        Core.forEachChild(node, child -> found[0] |= mentions(child, name));
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
    private record WalkAt(Core seed, Core container, Core.Block step, BindingId carried) {

        /** {@code e} as a walk, or null where it applies none, or its step is no closure written
         *  at it. */
        static WalkAt of(Core e) {
            AnOperationApplied applied = AnOperationApplied.of(e);
            if (applied == null) {
                return null;
            }
            Reductions.Reduction walk = Reductions.of(applied.operation());
            Combinator handing = Combinators.of(applied.operation());
            if (walk == null || handing == null) {
                return null;
            }
            List<Core> args = applied.args();
            if (walk.seedArg() >= args.size() || handing.containerArg() >= args.size()
                    || handing.closureArg() >= args.size()
                    || !(Core.withoutStanding(args.get(handing.closureArg()))
                            instanceof Core.Block step)
                    || walk.accumulatorParam() >= step.params().size()) {
                return null;
            }
            return new WalkAt(args.get(walk.seedArg()), args.get(handing.containerArg()), step,
                    step.params().get(walk.accumulatorParam()).binding());
        }
    }
}
