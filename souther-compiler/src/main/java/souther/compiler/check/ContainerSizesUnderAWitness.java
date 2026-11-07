package souther.compiler.check;

import souther.compiler.abort.GetsPast;
import souther.compiler.core.Core;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.Combinator;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.PieceOfAnElement;
import souther.compiler.semantics.WhereAnOperatorAnswers;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.values.TextExtents;

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
    private final Function<Core, Optional<BigInteger>> ofEachElementOfTheInput;
    private final Map<BindingId, Core> boundTo = new HashMap<>();
    private final Map<BindingId, Core> carriedBy = new HashMap<>();
    private final Set<Core> asking = new HashSet<>();

    private ContainerSizesUnderAWitness(Core within,
                                        Function<Core, Optional<BigInteger>> ofTheInput,
                                        Function<Core, Optional<BigInteger>> ofEachElement) {
        this.ofTheInput = ofTheInput;
        this.ofEachElementOfTheInput = ofEachElement;
        names(within);
    }

    /**
     * The most the collection {@code collection} holds on any run, read off how it is built
     * alone: a collection written out, one an arm of a match or a branch of a fork chooses,
     * one assembled of what is written. Nothing where it is built of a collection of the input,
     * whose size nothing here bounds.
     */
    public static Optional<BigInteger> mostHeldWhateverTheInputHolds(Core collection) {
        return new ContainerSizesUnderAWitness(collection, node -> Optional.empty(),
                node -> Optional.empty()).most(collection);
    }

    /**
     * Whether {@code operator}, standing in {@code within} and answering where {@code fits} says,
     * answers on every run whose input collections hold no more than {@code ofTheInput} says.
     *
     * @param ofTheInput    the most a collection of the input read at a node holds on such a run,
     *                      or nothing where the node reads no collection of the input or nothing
     *                      bounds it
     * @param ofEachElement the same, of the most each element of such a collection holds
     */
    public static boolean answersOn(Core within, Core operator, GetsPast completion,
                                    Function<Core, Optional<BigInteger>> ofTheInput,
                                    Function<Core, Optional<BigInteger>> ofEachElement) {
        ContainerSizesUnderAWitness reading =
                new ContainerSizesUnderAWitness(within, ofTheInput, ofEachElement);
        return switch (completion) {
            case GetsPast.Always _ -> true;
            case GetsPast.WhereTheAnswerFits(LinearForm<LawNumber<Integer>> answer) ->
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
            // How long a text a conversion makes turns on the text, and what a run holds of
            // collections says nothing of it.
            case GetsPast.WhereTheTextFits _ -> false;
            case GetsPast.NotKnown _ -> false;
        };
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
                Core walk = carriedBy.get(name.binding());
                if (walk != null) {
                    yield carried(WalkAt.of(walk), true);
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
                WalkAt walk = WalkAt.of(node);
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
        Core walking = whole instanceof Core.Read name ? carriedBy.get(name.binding()) : null;
        boolean handed = walking != null;
        WalkAt walk = WalkAt.of(handed ? walking : whole);
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
                instanceof GetsPast.WhereTheAnswerFits(LinearForm<LawNumber<Integer>> size))) {
            return Optional.empty();
        }
        AnOperationApplied applied = AnOperationApplied.of(node);
        if (applied == null) {
            return Optional.empty();
        }
        List<Core> operands = applied.args();
        // What is carried, counted once and as it is; every other operand reads none of it.
        Integer carriedAt = null;
        for (int at = 0; at < operands.size(); at++) {
            Core operand = Core.withoutStanding(operands.get(at));
            LawNumber<Integer> itsSize = new LawNumber.SizeOf<>(new LawSubject.Argument<>(at));
            if (carriedAt == null && operand instanceof Core.Read name
                    && name.binding().equals(carried)
                    && ExactRatio.ONE.equals(size.coefs().get(itsSize))) {
                carriedAt = at;
            } else if (mentions(operand, carried)) {
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
                    step.params().get(walk.accumulatorParam()));
        }
    }
}
