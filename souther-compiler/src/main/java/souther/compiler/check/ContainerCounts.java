package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.PieceOfAnElement;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * What a rule says of how many its value's containers hold, read through the library's laws: a
 * form over how many a container holds and how many different values its elements come to,
 * held against nought.
 *
 * <p>The laws and not the spellings. {@code List.allDistinctBy(k, xs)} is true exactly where as many
 * different answers of {@code k} come of the elements as there are elements, and
 * {@code List.length(List.distinctBy(k, xs)) == List.length(xs)} says that in so many words; a
 * reader that knew the call and the comparison as two shapes would answer for whichever one it had
 * learnt. So a number is read as the law of the operation answering it says
 * ({@link OperationLaw.Size}), a call's truth as its law says ({@link OperationLaw.Observation}),
 * and a container whose elements are each the image of a source's element ({@link
 * PieceOfAnElement#THE_CLOSURES_ANSWER}) is read as that source, with what its elements are
 * counted at taken through the image — so the different values of {@code List.map(.id, xs)} are
 * the different {@code id}s of {@code xs}.
 *
 * <p>Over places, and the arithmetic a rule writes over them. A place is a value read off a binding
 * by a run of fields, named as a place of a value names its fields ({@link ElementsApart#readOff});
 * anything else a rule counts is a number this does not name, and the whole reading is then null:
 * a statement with a part left out would be a different statement.
 *
 * <p>No reading of the declarations is held. A name a binding made is the binding, and two counts of
 * one name are counts of one value; what the name stands for is the asker's to follow.
 */
public final class ContainerCounts {

    /** A value read off a binding by a run of fields. Two of these are one value where they are
     *  equal, which is what lets the counts of one place cancel. */
    public record Place(BindingId binding, List<String> run) {

        public Place {
            Objects.requireNonNull(binding, "a place is read off some binding");
            run = List.copyOf(run);
        }
    }

    /** One number a rule counts of a place. */
    public sealed interface Count {

        /** Where it is counted. */
        Place at();

        /** How many the container at {@code at} holds. */
        record Size(Place at) implements Count {}

        /** How many different values the elements of the container at {@code at} come to, at the
         *  run of fields {@code run} of an element — empty for the element itself. */
        record Different(Place at, List<String> run) implements Count {

            public Different {
                run = List.copyOf(run);
            }
        }
    }

    /**
     * A rule's statement: {@code form} stands {@code rel} to nought.
     *
     * @param written the expression each place was written as, the first time it was met, for a
     *                reader asking about the place in its own terms. Not part of what is stated.
     */
    public record Stated(LinearForm<Count> form, Rel rel, Map<Place, Core> written) {

        public Stated {
            Objects.requireNonNull(form, "a statement is about some form");
            Objects.requireNonNull(rel, "and stands some way to nought");
            written = Map.copyOf(written);
        }
    }

    private final DeclarationNewtypes newtypes;
    private final Map<Place, Core> written = new LinkedHashMap<>();

    private ContainerCounts(DeclarationNewtypes newtypes) {
        this.newtypes = newtypes;
    }

    /**
     * What {@code compares} states of counts, or null where a side is no number this names.
     *
     * @param newtypes how a newtype's own {@code value} is named, null for as written
     */
    public static Stated of(StatedComparison compares, DeclarationNewtypes newtypes) {
        ContainerCounts reading = new ContainerCounts(newtypes);
        LinearForm<Count> left = reading.number(compares.left());
        LinearForm<Count> right = left == null ? null : reading.number(compares.right());
        LinearForm<Count> form = right == null ? null : left.minus(right).orNull();
        return form == null ? null
                : new Stated(form, compares.relationUnder(true), reading.written);
    }

    /**
     * What {@code call} coming out {@code positive} states of counts, as the law settling its truth
     * says — or null where no law states it as a comparison of numbers this names.
     */
    public static Stated ofTheTruth(Core.PreservedCall call, boolean positive,
                                    DeclarationNewtypes newtypes) {
        if (!(DefaultBoundOperationFacts.get().settled(call.operation(),
                OperationLaw.Observed.TRUTH) instanceof BoundOperationFacts.Settled.ByALaw(
                        OperationLaw.Observation<DeclaredArgument>(AnswerAspect aspect,
                                LawProposition.Compared<DeclaredArgument>(var law, Rel states)),
                        var _))
                || aspect != AnswerAspect.TRUTH) {
            return null;
        }
        ContainerCounts reading = new ContainerCounts(newtypes);
        AnOperationApplied applied = AnOperationApplied.of(call);
        LinearForm<Count> form = law.over(number -> reading.lawNumber(applied, number));
        return form == null ? null
                : new Stated(form, positive ? states : states.denied(), reading.written);
    }

    /** {@code e} as a form over counts, or null where it is no number this names. */
    private LinearForm<Count> number(Core e) {
        Core bare = Core.withoutStanding(e);
        switch (bare) {
            case Core.Int literal -> {
                return LinearForm.constant(ExactRatio.of(literal.value()));
            }
            case Core.Neg negated -> {
                LinearForm<Count> of = number(negated.operand());
                return of == null ? null : of.negate();
            }
            case Core.Binary bin when bin.op() == BinOp.ADD || bin.op() == BinOp.SUB -> {
                LinearForm<Count> left = number(bin.left());
                LinearForm<Count> right = left == null ? null : number(bin.right());
                if (right == null) {
                    return null;
                }
                return (bin.op() == BinOp.ADD ? left.plus(right) : left.minus(right)).orNull();
            }
            case Core.Binary bin when bin.op() == BinOp.MUL -> {
                LinearForm<Count> left = number(bin.left());
                LinearForm<Count> right = left == null ? null : number(bin.right());
                if (right == null) {
                    return null;
                }
                // A product is a form only where one side is a constant.
                if (left.coefs().isEmpty()) {
                    return right.times(left.constant()).orNull();
                }
                return right.coefs().isEmpty() ? left.times(right.constant()).orNull() : null;
            }
            default -> {
                Core counted = countedBy(bare);
                return counted == null ? null : count(counted);
            }
        }
    }

    /** What {@code e} counts the elements of, or null where it is no such count. */
    private static Core countedBy(Core e) {
        AnOperationApplied applied = AnOperationApplied.of(e);
        BoundOperationFact.AnswersANumberTakenOfAValueItIsGiven taken = applied == null ? null
                : DefaultBoundOperationFacts.get().numberTakenOf(applied.operation());
        return taken != null && taken.how() instanceof TakenAs.HowManyItHolds
                ? applied.argument(taken.of()) : null;
    }

    /** How many {@code container} holds, as a form over counts. */
    private LinearForm<Count> count(Core container) {
        Place at = place(container);
        if (at != null) {
            return LinearForm.atom(new Count.Size(at));
        }
        AnOperationApplied applied = AnOperationApplied.of(container);
        if (applied == null || !(DefaultBoundOperationFacts.get().settled(applied.operation(),
                OperationLaw.Observed.SIZE) instanceof BoundOperationFacts.Settled.ByALaw(
                        OperationLaw.Size<DeclaredArgument> law, var _))) {
            return null;
        }
        LinearForm<LawNumber<DeclaredArgument>> unconditional = law.unconditional();
        return unconditional == null ? null
                : unconditional.over(number -> lawNumber(applied, number));
    }

    /** A number a law names over the arguments of {@code applied}, as a form over counts. */
    private LinearForm<Count> lawNumber(AnOperationApplied applied,
                                        LawNumber<DeclaredArgument> number) {
        return switch (number) {
            case LawNumber.SizeOf<DeclaredArgument>(
                    LawSubject.Argument<DeclaredArgument>(DeclaredArgument of)) -> {
                Core given = applied.argument(of);
                yield given == null ? null : count(given);
            }
            case LawNumber.AnArgument<DeclaredArgument>(DeclaredArgument of) -> {
                Core given = applied.argument(of);
                yield given == null ? null : number(given);
            }
            case LawNumber.HowManyDifferent<DeclaredArgument>(DeclaredArgument over,
                    LawSubject<DeclaredArgument> each) -> {
                Core container = applied.argument(over);
                List<Step> read = container == null ? null : readOfAnElement(applied, over, each);
                yield read == null ? null : different(container, read);
            }
            default -> null;
        };
    }

    /**
     * What a law counts of an element of the argument at {@code over}: the element itself, a key
     * of it, or what a closure answers of it — as the steps taken into the element, or null where it
     * is none of these.
     */
    private List<Step> readOfAnElement(AnOperationApplied applied, DeclaredArgument over,
                                       LawSubject<DeclaredArgument> each) {
        return switch (each) {
            case LawSubject.ElementOf<DeclaredArgument>(var of) when of.equals(over) -> List.of();
            // A key is the first of the two an element of a list of entries pairs.
            case LawSubject.KeyOf<DeclaredArgument>(var of) when of.equals(over) ->
                    List.of(new Step.Component(0));
            case LawSubject.WhatTheClosureAnswers<DeclaredArgument>(var closure) -> {
                Core given = applied.argument(closure);
                yield given == null ? null : through(given, List.of());
            }
            default -> null;
        };
    }

    /**
     * How many different values the elements of {@code container} come to, each read by
     * {@code read}, as a form over counts.
     *
     * <p>A container each of whose elements is the image of a source's element is read as the
     * source, with {@code read} taken through the image: an element of {@code List.map(f, xs)} is
     * {@code f} of an element of {@code xs}, so what is read of it is what is read of {@code f}'s
     * answer. Only where the image is one element for one, as the library says the operation puts
     * its answer together; a filter keeps some elements and not others, and the different values
     * of what it keeps are not those of its source.
     */
    private LinearForm<Count> different(Core container, List<Step> read) {
        Place at = place(container);
        if (at != null) {
            List<String> run = fieldsOf(read);
            return run == null ? null : LinearForm.atom(new Count.Different(at, run));
        }
        AnOperationApplied applied = AnOperationApplied.of(container);
        BoundOperationFacts.Assembled assembled = applied == null ? null
                : DefaultBoundOperationFacts.get().assembles(applied.operation());
        if (assembled == null || assembled.piece() != PieceOfAnElement.THE_CLOSURES_ANSWER) {
            return null;
        }
        Core source = applied.argument(assembled.source());
        Core image = applied.argument(assembled.closure());
        List<Step> inTheSource = source == null || image == null ? null : through(image, read);
        return inTheSource == null ? null : different(source, inTheSource);
    }

    /** One step into a value: a field of a record or a component of a tuple. */
    private sealed interface Step {

        record Field(String name) implements Step {}

        record Component(int index) implements Step {}
    }

    /**
     * What {@code read} of the answer of {@code closure} is, as steps into the element it is handed
     * — or null where the closure does anything else with it.
     *
     * <p>Through what the closure builds, and down what it reads: {@code x -> (x.id, x)} read at
     * its first component is {@code x.id}, and {@code x -> x.line} read at {@code sku} is
     * {@code x.line.sku}.
     */
    private List<Step> through(Core closure, List<Step> read) {
        if (!(Core.withoutStanding(closure) instanceof Core.Block block)
                || block.params().size() != 1 || block.params().getFirst().binding() == null) {
            return null;
        }
        Core at = Core.withoutStanding(block.body());
        int taken = 0;
        while (taken < read.size()) {
            Core inside = into(at, read.get(taken));
            if (inside == null) {
                break;
            }
            at = Core.withoutStanding(inside);
            taken++;
        }
        ElementsApart.ReadOff off = ElementsApart.readOff(at, newtypes);
        if (!(Core.withoutStanding(off.holder()) instanceof Core.Read param)
                || !param.binding().equals(block.params().getFirst().binding())) {
            return null;
        }
        List<Step> out = new ArrayList<>();
        off.path().steps().forEach(field -> out.add(new Step.Field(field)));
        out.addAll(read.subList(taken, read.size()));
        return out;
    }

    /** What {@code built} holds at {@code step}, where it is a tuple or a record it builds; null
     *  where it builds neither, or nothing there. */
    private static Core into(Core built, Step step) {
        Core bare = Core.withoutStanding(built);
        return switch (step) {
            case Step.Component(int index) when bare instanceof Core.Tuple tuple
                    && index < tuple.elements().size() -> tuple.elements().get(index);
            case Step.Field(String name) when bare instanceof Core.Construct record ->
                    record.values().stream().filter(each -> each.field().equals(name))
                            .map(Core.FieldValue::value).findFirst().orElse(null);
            default -> null;
        };
    }

    /** The fields {@code read} takes, or null where it takes a component of a tuple. */
    private static List<String> fieldsOf(List<Step> read) {
        List<String> out = new ArrayList<>();
        for (Step each : read) {
            if (!(each instanceof Step.Field(String name))) {
                return null;
            }
            out.add(name);
        }
        return out;
    }

    /** The place {@code e} is, or null where it is not read off a binding by fields. */
    private Place place(Core e) {
        ElementsApart.ReadOff off = ElementsApart.readOff(e, newtypes);
        if (!(Core.withoutStanding(off.holder()) instanceof Core.Read read)) {
            return null;
        }
        Place at = new Place(read.binding(), off.path().steps());
        written.putIfAbsent(at, e);
        return at;
    }
}
