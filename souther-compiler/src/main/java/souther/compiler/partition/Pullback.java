package souther.compiler.partition;

import souther.compiler.check.BooleanMeaning;
import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.Choice;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.ElementWitness;
import souther.compiler.check.Location;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.StatedComparison;
import souther.compiler.core.Core;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.InputTruth;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.semantics.SideAnswered;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.function.Supplier;

/**
 * What a condition states about the subjects it is finally about, read off the tree where the
 * language's operations stand.
 *
 * <p>The one reading of what a condition means. What is asked of a value the body derived — that it
 * holds, that it holds anything, that it holds a value — is carried back through how the value was
 * derived, one step at a time, to a question about a position of the input; and a step is taken only
 * where the construct's own semantics or a law the library declares makes the two questions one.
 * Where none does, the part is left as unread and says why ({@link Proposition.Unread}), and nothing
 * past it is guessed.
 *
 * <p><b>The steps.</b> A name or a {@code let} is what it stands for. A denial asks the other way
 * round. A conjunction, a disjunction, an {@code if} and a {@code match} are what their parts state,
 * joined the way the construct joins them. A size held against a number that parts nought from every
 * size above it asks whether the container holds anything ({@link AnEmptinessCheck#checked}).
 * An operation walking a container with a closure comes out the way some element witnesses
 * ({@link ElementWitness}), and one that answers as many as it was handed holds something exactly
 * where what it was handed does. What is left is a comparison, a truth, a case or a value being there
 * at a subject a row controls — the parts a proposition is made of.
 *
 * <p>Each part is kept with the expression it was read off, in the order it was met ({@link Leaf}),
 * so a reader asking what a fork turns on and a reader sending an author to a part have what they
 * need without reading the condition a second time.
 */
final class Pullback {

    /**
     * A part of what a condition states, and the expression it was read off, where it stands.
     *
     * @param part what the part states, the way round it was met
     * @param from the expression, read in the names that hold where it stands
     */
    record Leaf(Proposition part, Denotation from) {}

    /**
     * What a condition states, and the parts it was read from.
     *
     * @param proposition what holds where the condition does
     * @param leaves      every part met, in the order met — a part met twice is here twice
     */
    record Pulled(Proposition proposition, List<Leaf> leaves) {

        /**
         * The parts the truth of {@link #proposition} turns on, each with where it was read off.
         *
         * <p>Read off the proposition and not off the parts met. A part a choice left out — an arm
         * of an {@code if} whose condition always fails, a conjunct beside one that never holds —
         * was met and turns nothing; and a part that comes out the same whatever the input is an
         * answer and not a question. Some element meeting a part turns on that part, and on whether
         * there is an element only through it: what no element decides was taken out of the
         * quantifier where it was made, so the container is a part wherever it is one.
         */
        List<Leaf> turnsOn() {
            Set<String> parts = new HashSet<>();
            partsOf(proposition, parts);
            return leaves.stream().filter(leaf -> parts.contains(leaf.part().key())).toList();
        }

        /** The spelling of each part {@code stated} turns on, either way round, into {@code into}. */
        private static void partsOf(Proposition stated, Set<String> into) {
            switch (stated) {
                case Proposition.Always _ -> { }
                case Proposition.Unread unread when unread.fixed() -> { }
                case Proposition.All all -> all.parts().forEach(part -> partsOf(part, into));
                case Proposition.Any any -> any.parts().forEach(part -> partsOf(part, into));
                case Proposition.Some some -> partsOf(some.ofTheElement(), into);
                default -> {
                    into.add(stated.key());
                    into.add(stated.denied().key());
                }
            }
        }
    }

    private final InputReading read;
    private final Optional<ModelOccurrence> where;
    private final List<Leaf> leaves = new ArrayList<>();
    private final Set<TermPath> quantifying = new HashSet<>();
    /**
     * Where whether a container holds anything was asked, while what it holds is being read.
     *
     * <p>What a size of a position is read off is the expression that asked about it — the check or
     * the comparison an author wrote — and not the position: a fork asking whether a list holds
     * anything is answered for by whoever reads that question, and a position as a whole is no
     * reader of it.
     */
    private Denotation askedAt;
    private int unread;

    private Pullback(InputReading read, Optional<ModelOccurrence> where) {
        this.read = read;
        this.where = where;
    }

    /**
     * What {@code truth} holding states.
     *
     * @param where the construct of the model the condition is, where the caller knows it
     */
    static Pulled ofATruth(Core truth, InputReads reads, InputReading read,
                           Optional<ModelOccurrence> where) {
        Pullback reading = new Pullback(read, where);
        Proposition stated = reading.observe(truth, AnswerAspect.TRUTH, reads);
        return new Pulled(stated, List.copyOf(reading.leaves));
    }

    /**
     * What a comparison the source wrote states, read as any truth is: a size held where it parts
     * nought from every size above it is whether the container holds anything.
     */
    static Pulled ofAComparison(StatedComparison comparison, InputReads reads, InputReading read,
                                Optional<ModelOccurrence> where) {
        Pullback reading = new Pullback(read, where);
        AnEmptinessCheck.Checked checked = AnEmptinessCheck.checked(comparison);
        Proposition stated;
        if (checked != null) {
            Proposition some = reading.observe(checked.container(), AnswerAspect.EMPTINESS, reads);
            stated = checked.emptyWhereItHolds() ? some.denied() : some;
        } else {
            stated = reading.compared(comparison, false, reads);
        }
        return new Pulled(stated, List.copyOf(reading.leaves));
    }

    /**
     * Whether what a written comparison states was carried past it to the input — so that what it
     * states is the parts it was carried to, and not a rule the comparison draws of its own.
     *
     * <p>Only an emptiness check is carried anywhere: any other comparison is the relation it
     * states. And one is carried past only where the container it asks about is no position of its
     * own and every part it was carried to was read — one that stopped on the way is a rule about a
     * value made from the input, which the comparison still is.
     */
    static boolean carriesPast(StatedComparison comparison, InputReads reads, InputReading read) {
        if (AnEmptinessCheck.checked(comparison) == null) {
            return false;
        }
        Pulled pulled = ofAComparison(comparison, reads, read, Optional.empty());
        return !(pulled.proposition() instanceof Proposition.Compared)
                && pulled.turnsOn().stream()
                        .noneMatch(leaf -> leaf.part() instanceof Proposition.Unread);
    }

    /** What {@code container} holding something states. */
    static Pulled ofHoldingSomething(Core container, InputReads reads, InputReading read,
                                     Optional<ModelOccurrence> where) {
        Pullback reading = new Pullback(read, where);
        Proposition stated = reading.observe(container, AnswerAspect.EMPTINESS, reads);
        return new Pulled(stated, List.copyOf(reading.leaves));
    }

    /**
     * What {@code e} coming out {@code holds} on {@code aspect} states: holding, holding something,
     * holding a value.
     */
    private Proposition observe(Core standing, AnswerAspect aspect, InputReads reads) {
        Core e = Core.withoutStanding(standing);
        switch (e) {
            case Core.LetIn let -> {
                return observe(let.body(), aspect, reads.and(let.binder(), let.value()));
            }
            case Core.Read name when reads.meaningOf(name, read.rules().symbols(),
                    read.rules().newtypes()) instanceof ReadMeaning.Through through -> {
                return observe(through.denotes().value(), aspect, through.denotes().at());
            }
            case Core.If iff -> {
                Proposition cond = observe(iff.cond(), AnswerAspect.TRUTH, reads);
                return Proposition.any(List.of(
                        Proposition.all(List.of(cond, observe(iff.then(), aspect, reads))),
                        Proposition.all(List.of(cond.denied(), observe(iff.els(), aspect, reads)))));
            }
            case Core.Match match -> {
                return ofAMatch(match, aspect, reads);
            }
            default -> { }
        }
        return switch (aspect) {
            case TRUTH -> truth(e, reads);
            case EMPTINESS -> holdingSomething(e, reads);
            case PRESENCE -> present(e, reads);
        };
    }

    /** What a truth that is no binding, name or choice states. */
    private Proposition truth(Core standing, InputReads reads) {
        Core e = Core.withoutStanding(standing);
        if (e instanceof Core.Bool written) {
            return new Proposition.Always(written.value());
        }
        Optional<BooleanMeaning.UnderADenial> denied = BooleanMeaning.underADenial(e, true);
        if (denied.isPresent()) {
            Proposition under = observe(denied.get().part(), AnswerAspect.TRUTH, reads);
            return denied.get().positive() ? under : under.denied();
        }
        Optional<Boolean> folded = BooleanMeaning.folded(e, read.rules().symbols());
        if (folded.isPresent()) {
            return new Proposition.Always(folded.get());
        }
        if (e instanceof Core.Binary binary) {
            Optional<ConditionJoin> joined = ConditionJoin.of(binary.op());
            if (joined.isPresent()) {
                List<Proposition> parts = List.of(observe(binary.left(), AnswerAspect.TRUTH, reads),
                        observe(binary.right(), AnswerAspect.TRUTH, reads));
                return joined.get().under(true) == ConditionJoin.BOTH
                        ? Proposition.all(parts) : Proposition.any(parts);
            }
        }
        TermPath position = InputTruth.positionOf(e, reads, read.rules().newtypes());
        if (position != null) {
            return leaf(new Proposition.Truth(new DecisionSubject.AnInput(position), true), e,
                    reads);
        }
        Optional<StatedComparison> stated = BooleanMeaning.asAComparison(e);
        if (stated.isPresent()) {
            AnEmptinessCheck.Checked checked = AnEmptinessCheck.checked(stated.get());
            if (checked != null) {
                Proposition some = asking(new Denotation(e, reads),
                        () -> observe(checked.container(), AnswerAspect.EMPTINESS, reads));
                return checked.emptyWhereItHolds() ? some.denied() : some;
            }
            return leaf(compared(stated.get(), fixed(e, reads), reads), e, reads);
        }
        AnOperationApplied applied = AnOperationApplied.of(e);
        if (applied != null) {
            Proposition witnessed = witnessed(applied, e, AnswerAspect.TRUTH, reads);
            if (witnessed != null) {
                return witnessed;
            }
            Proposition member = membership(applied, e, reads);
            if (member != null) {
                return member;
            }
        }
        return unread(e, reads, new OnTheWay.Why.NoWordsForTheShape());
    }

    /** What a container that is no binding, name or choice holding something states. */
    private Proposition holdingSomething(Core standing, InputReads reads) {
        Core e = Core.withoutStanding(standing);
        switch (e) {
            case Core.ListLit list -> {
                return new Proposition.Always(!list.elements().isEmpty());
            }
            case Core.Str text -> {
                return new Proposition.Always(!text.value().isEmpty());
            }
            default -> { }
        }
        AnOperationApplied applied = AnOperationApplied.of(e);
        if (applied != null) {
            Proposition witnessed = witnessed(applied, e, AnswerAspect.EMPTINESS, reads);
            if (witnessed != null) {
                return witnessed;
            }
            DeclaredArgument kept = DefaultBoundOperationFacts.get()
                    .keepsWhetherItHoldsAnything(applied.operation());
            Core source = kept == null ? null : applied.argument(kept);
            if (source != null) {
                return observe(source, AnswerAspect.EMPTINESS, reads);
            }
        }
        // What the container's holding anything is read off, or where reading it stopped, is the
        // question that asked it, where something asked it.
        Denotation asked = askedAt != null ? askedAt : new Denotation(e, reads);
        if (reads.pathOf(e, read.rules().newtypes()) instanceof PathResolution.At(TermPath held)) {
            Proposition some = holdsSomethingAt(held);
            return leaf(some != null ? some
                    : unreadPart(new OnTheWay.Why.SizeOfTheContainerNotStated(),
                            fixed(e, reads)), asked);
        }
        return leaf(unreadPart(new OnTheWay.Why.NoWordsForTheShape(), fixed(e, reads)), asked);
    }

    /** What an optional that is no binding, name or choice holding a value states. */
    private Proposition present(Core standing, InputReads reads) {
        Core e = Core.withoutStanding(standing);
        switch (e) {
            case Core.OptionSome _ -> {
                return new Proposition.Always(true);
            }
            case Core.OptionNone _ -> {
                return new Proposition.Always(false);
            }
            default -> { }
        }
        AnOperationApplied applied = AnOperationApplied.of(e);
        if (applied != null) {
            Proposition witnessed = witnessed(applied, e, AnswerAspect.PRESENCE, reads);
            if (witnessed != null) {
                return witnessed;
            }
        }
        if (reads.pathOf(e, read.rules().newtypes()) instanceof PathResolution.At(TermPath at)) {
            return leaf(new Proposition.Present(new DecisionSubject.AnInput(at), true), e, reads);
        }
        return unread(e, reads, new OnTheWay.Why.NoWordsForTheShape());
    }

    /**
     * What a match answering {@code aspect} states: some arm taken, and what that arm answers.
     *
     * <p>An arm is taken where the value is one of its cases and none of an arm before it. Which
     * cases a value written in the source is is settled before any row ({@link
     * InputReads#whetherEveryRowTakes}); one at a position is a case the row writes there.
     */
    private Proposition ofAMatch(Core.Match match, AnswerAspect aspect, InputReads reads) {
        Set<TypeSymbol> written = reads.casesWritten(match.scrutinee(),
                read.rules().symbols(), read.rules().newtypes());
        DecisionSubject subject = reads.pathOf(match.scrutinee(), read.rules().newtypes())
                instanceof PathResolution.At(TermPath at) ? new DecisionSubject.AnInput(at) : null;
        List<Proposition> taken = new ArrayList<>();
        List<Proposition> before = new ArrayList<>();
        for (Core.Case arm : match.cases()) {
            Proposition selects;
            Optional<Boolean> every = InputReads.whetherEveryRowTakes(arm, written);
            if (every.isPresent()) {
                selects = new Proposition.Always(every.get());
            } else if (arm.pattern() == null) {
                selects = new Proposition.Always(true);
            } else if (subject != null) {
                selects = new Proposition.InCases(subject, CasesLeft.selectedBy(arm.pattern()), true);
            } else {
                // Which arm is taken is the match's own reader's to classify, and no part offered
                // here: what is read is what the arms answer. Not the same whatever the input even
                // over values the source wrote out, since what is matched is one of several of them
                // and each may take another arm — one alone is settled above.
                selects = unreadPart(new OnTheWay.Why.ForkArmNotReadAsANarrowing(), false);
            }
            List<Proposition> arrives = new ArrayList<>(before.stream()
                    .map(Proposition::denied).toList());
            arrives.add(selects);
            InputReads inside = reads.choosing(Choice.Decides.ofCase(match, arm),
                    read.rules().symbols(), read.rules().newtypes());
            arrives.add(observe(arm.body(), aspect, inside));
            taken.add(Proposition.all(arrives));
            before.add(selects);
        }
        return Proposition.any(taken);
    }

    /**
     * What {@code applied} coming out on {@code aspect} states where the library declares the
     * element that witnesses it — or null where it declares none on that side.
     */
    private Proposition witnessed(AnOperationApplied applied, Core e, AnswerAspect aspect,
                                  InputReads reads) {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        ElementWitness law = facts.resultHasAnElementWitness(applied.operation());
        if (law == null || law.result().aspect() != aspect) {
            return null;
        }
        Core over = applied.argument(law.container());
        Core handed = applied.argument(law.closure());
        if (over == null || handed == null) {
            return null;
        }
        Proposition some = someElement(over, handed, law.ofTheClosure(), e, reads);
        return law.result().holds() ? some : some.denied();
    }

    /**
     * Some element of {@code over}, handed to the closure at {@code handed}, making it answer as
     * {@code witness}.
     */
    private Proposition someElement(Core over, Core handed, SideAnswered witness, Core e,
                                    InputReads reads) {
        Denotation closure = reads.denotes(handed, read.rules().symbols(), read.rules().newtypes());
        if (!(Core.withoutStanding(closure.value()) instanceof Core.Block block)) {
            return unread(e, reads, new OnTheWay.Why.NoWordsForTheShape());
        }
        Denotation container = reads.standing(over, read.rules().symbols(),
                read.rules().newtypes());
        // A container the source wrote out has no element where it is empty. Otherwise what the
        // closure is handed is one of the written values, which is how the reading of the input
        // reads its parameter ({@code ReadMeaning.OneOf}) for every reader of the closure: what it
        // states of the input is what it states of any of them.
        if (Core.withoutStanding(container.value()) instanceof Core.ListLit list) {
            if (list.elements().isEmpty()) {
                return new Proposition.Always(false);
            }
            Proposition answered = observe(block.body(), witness.aspect(), closure.at());
            return witness.holds() ? answered : answered.denied();
        }
        if (!(reads.pathOf(over, read.rules().newtypes()) instanceof PathResolution.At(
                TermPath held))) {
            return unread(over, reads, new OnTheWay.Why.ContainerAtNoPosition());
        }
        // The element is what stands at the container's element inside the closure, so the same
        // container quantified inside itself would name two elements one subject.
        if (!quantifying.add(held)) {
            return unread(e, reads, new OnTheWay.Why.NoWordsForTheShape());
        }
        Proposition answered;
        try {
            answered = observe(block.body(), witness.aspect(), closure.at());
        } finally {
            quantifying.remove(held);
        }
        Proposition ofTheElement = witness.holds() ? answered : answered.denied();
        return someElementMeeting(held, ofTheElement, () -> {
            Proposition some = holdsSomethingAt(held);
            return some != null ? leaf(some, askedAt != null ? askedAt : new Denotation(e, reads))
                    : unread(over, reads, new OnTheWay.Why.SizeOfTheContainerNotStated());
        });
    }

    /**
     * Some element of the container at {@code held} meeting {@code ofTheElement}, with what no
     * element decides taken out of the quantifier.
     *
     * <p>What comes out the same for every element is itself and there being an element at all —
     * one that never holds settles it, one that always does leaves whether there is an element. A
     * disjunct no element decides is that disjunct and there being an element, beside some element
     * meeting the rest; a conjunct is that conjunct, beside some element meeting the rest. Left
     * inside, whether the container holds anything would be something the proposition turns on that
     * none of its parts names, and a reader of the parts would hand nobody the container.
     *
     * @param holdsSomething that the container holds something, asked for only where it is a part
     */
    private static Proposition someElementMeeting(TermPath held, Proposition ofTheElement,
                                                  Supplier<Proposition> holdsSomething) {
        if (!ofTheElement.mayTurnOnAnElementOf(held)) {
            return ofTheElement instanceof Proposition.Always(boolean holds) && !holds
                    ? ofTheElement
                    : Proposition.all(List.of(ofTheElement, holdsSomething.get()));
        }
        List<Proposition> parts = switch (ofTheElement) {
            case Proposition.All all -> all.parts();
            case Proposition.Any any -> any.parts();
            default -> List.of(ofTheElement);
        };
        List<Proposition> decided = parts.stream()
                .filter(part -> !part.mayTurnOnAnElementOf(held)).toList();
        if (decided.isEmpty()) {
            return new Proposition.Some(held, ofTheElement, true);
        }
        List<Proposition> undecided = parts.stream()
                .filter(part -> part.mayTurnOnAnElementOf(held)).toList();
        return ofTheElement instanceof Proposition.Any
                ? Proposition.any(List.of(
                        someElementMeeting(held, Proposition.any(decided), holdsSomething),
                        new Proposition.Some(held, Proposition.any(undecided), true)))
                : Proposition.all(List.of(Proposition.all(decided),
                        new Proposition.Some(held, Proposition.all(undecided), true)));
    }

    /**
     * What a container holding the value {@code applied} asks about states: some element the same
     * as it — or null where {@code applied} asks no such thing.
     */
    private Proposition membership(AnOperationApplied applied, Core e, InputReads reads) {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        DeclaredArgument asked = facts.asksWhetherItsContainerHolds(applied.operation());
        var reads0 = facts.readsItsContainer(applied.operation());
        if (asked == null || reads0 == null) {
            return null;
        }
        Core over = applied.argument(reads0.container());
        if (!(reads.pathOf(over, read.rules().newtypes()) instanceof PathResolution.At(
                TermPath held))) {
            return unread(over, reads, new OnTheWay.Why.ContainerAtNoPosition());
        }
        if (!(reads.pathOf(applied.argument(asked), read.rules().newtypes())
                instanceof PathResolution.At(TermPath value))) {
            return unread(e, reads, new OnTheWay.Why.ValueAtNoPosition());
        }
        Proposition same = leaf(new Proposition.SameValue(
                new DecisionSubject.AnInput(held.element()), new DecisionSubject.AnInput(value),
                true), e, reads);
        return new Proposition.Some(held, same, true);
    }

    /** That the container at {@code held} holds something, as its size above nought — or null
     *  where its size is no term of this input. */
    private Proposition holdsSomethingAt(TermPath held) {
        Type container = read.domain().typeAt(held, read.rules());
        ValueName.Stdlib size = container == null ? null
                : NumericMeasures.takenOf(container, read.rules().inners());
        NumericTerm.TakenOf count = size == null ? null : NumericTerm.TakenOf.of(size, held,
                container, read.rules().inners(), read.rules().symbols());
        if (count == null) {
            return null;
        }
        LinearForm<Quantity> form =
                LinearForm.<Quantity>atom(new DecisionAtom.OfTheInput(count));
        return new Proposition.Compared(new Relation.Affine(form, Rel.GT), true);
    }

    /**
     * A comparison over values the body bound, as the relation it states over them — or unread
     * where it is over anything else.
     *
     * <p>Asked where the arithmetic of the input read nothing, which is where what a value is
     * computed from is unknown: a dependency's answer, what an attempt built. Which value it is is
     * still known, by the binding that names it, and two comparisons over one name are about one
     * number. A comparison mixing such a value with a position of the input is not read here.
     */
    private Proposition ofBoundValues(StatedComparison comparison, boolean fixed,
                                      InputReads reads) {
        // A comparison whose answer is the same on every run is no relation between numbers that
        // vary: what it compares can be a parameter of a closure applied to elements written out,
        // and that name stands for a different value each time it is applied.
        if (fixed) {
            return unreadPart(new OnTheWay.Why.ComparisonNotRepresentedAsACut(), true);
        }
        LinearForm<Quantity> left = boundForm(comparison.left(), reads);
        LinearForm<Quantity> right = boundForm(comparison.right(), reads);
        LinearForm<Quantity> form = left == null || right == null ? null
                : left.minus(right).orNull();
        if (form == null || form.coefs().isEmpty()) {
            return unreadPart(new OnTheWay.Why.ComparisonNotRepresentedAsACut(), fixed);
        }
        Rel states = comparison.claim().statedRelation();
        Rel proposition = states.orItsDenial();
        return new Proposition.Compared(new Relation.Affine(form, proposition),
                states == proposition);
    }

    /** {@code side} as a number written out or a number of a value the body bound, or null. */
    private LinearForm<Quantity> boundForm(Core side, InputReads reads) {
        Core e = Core.withoutStanding(side);
        if (e instanceof Core.Int written) {
            return LinearForm.constant(ExactRatio.of(written.value()));
        }
        if (reads.pathOf(e, read.rules().newtypes()) instanceof PathResolution.At) {
            return null;
        }
        List<TermPath.Step> steps = new ArrayList<>();
        Core at = Core.withoutStanding(e);
        while (true) {
            if (at instanceof Core.FieldProjection projection) {
                at = Core.withoutStanding(projection.lastAccess());
            } else if (at instanceof Core.FieldAccess access) {
                if (Location.isStep(access.target().type(), access.field(),
                        read.rules().newtypes())) {
                    steps.addFirst(new TermPath.Step.Field(access.field()));
                }
                at = Core.withoutStanding(access.target());
            } else {
                break;
            }
        }
        // One value by its binding, and only where the name is one value on a run. A name handed
        // each element of a container, or one that can be any of several values, stands for a
        // different value each time it is read, so a relation over it relates nothing.
        if (!(Core.withoutStanding(at) instanceof Core.Read name)) {
            return null;
        }
        ReadMeaning stands = reads.meaningOf(name, read.rules().symbols(), read.rules().newtypes());
        if (stands instanceof ReadMeaning.Element || stands instanceof ReadMeaning.OneOf) {
            return null;
        }
        return LinearForm.atom(new Quantity.OfABinding(name.binding(), steps, side.type()));
    }

    /** A form over the input's numbers, as one over the quantities a relation is written over. */
    private static LinearForm<Quantity> asQuantities(LinearForm<DecisionAtom> form) {
        return new LinearForm<>(form.constant(), new LinkedHashMap<>(form.coefs()));
    }

    /**
     * A comparison as the relation it states over this input's quantities.
     *
     * <p>Off the same readings the arithmetic and a stopped reading are read by everywhere a
     * comparison is, so what it states here is what a border on it is drawn at.
     */
    private Proposition compared(StatedComparison comparison, boolean fixed, InputReads reads) {
        InputTruth truth = InputTruth.compared(comparison, true, reads, read.rules().symbols(),
                read.rules().newtypes());
        if (truth != null) {
            return new Proposition.Truth(new DecisionSubject.AnInput(truth.at()), truth.held());
        }
        return switch (AffineReading.read(comparison, read.domain(), reads, read.rules())) {
            case AffineReading.OfAComparison.Cuts(var affine) -> {
                Rel states = affine.claim().statedRelation();
                LinearForm<NumericTerm> against =
                        affine.form().minus(LinearForm.constant(affine.cut())).orNull();
                if (against == null) {
                    yield unreadPart(new OnTheWay.Why.ComparisonNotRepresentedAsACut(), fixed);
                }
                Rel proposition = states.orItsDenial();
                yield new Proposition.Compared(new Relation.Affine(
                        asQuantities(DecisionComparison.ofTheInput(against)), proposition),
                        states == proposition);
            }
            case AffineReading.OfAComparison.CutsNothing constant ->
                    new Proposition.Always(constant.holds(comparison.claim().statedRelation()));
            case AffineReading.OfAComparison.NotHeld _ -> ofBoundValues(comparison, fixed, reads);
            case AffineReading.OfAComparison.Stopped _ -> {
                ComparedLine drawn = ComparedLine.asWritten(comparison, read, reads);
                if (drawn == null) {
                    yield ofBoundValues(comparison, fixed, reads);
                }
                Rel states = drawn.claim().statedRelation();
                Rel proposition = states.orItsDenial();
                yield new Proposition.Compared(new Relation.Ordered(
                        new DecisionAtom.OfTheInput(drawn.term()), drawn.value(), proposition),
                        states == proposition);
            }
        };
    }

    /** {@code part}, kept with the expression it was read off. */
    private Proposition leaf(Proposition part, Core from, InputReads reads) {
        return leaf(part, new Denotation(from, reads));
    }

    private Proposition leaf(Proposition part, Denotation from) {
        if (!(part instanceof Proposition.Always)) {
            leaves.add(new Leaf(part, from));
        }
        return part;
    }

    /** {@code reading}, with whether a container holds anything asked at {@code where}. */
    private Proposition asking(Denotation where, Supplier<Proposition> reading) {
        Denotation outer = askedAt;
        askedAt = where;
        try {
            return reading.get();
        } finally {
            askedAt = outer;
        }
    }

    /** {@code e}, which nothing here reads the meaning of. */
    private Proposition unread(Core e, InputReads reads, OnTheWay.Why why) {
        return leaf(unreadPart(why, fixed(e, reads)), e, reads);
    }

    /**
     * Whether {@code e} is the same whatever the input, as far as what it is made of says: a value
     * written out, or an operator or an operation applied to values written out.
     */
    private boolean fixed(Core standing, InputReads reads) {
        Core e = Core.withoutStanding(standing);
        if (reads.writtenOut(e, read.rules().symbols(), read.rules().newtypes())) {
            return true;
        }
        if (e instanceof Core.Binary binary) {
            return fixed(binary.left(), reads) && fixed(binary.right(), reads);
        }
        AnOperationApplied applied = AnOperationApplied.of(e);
        return applied != null && applied.args().stream().allMatch(arg -> reads.writtenOut(arg,
                read.rules().symbols(), read.rules().newtypes()));
    }

    private Proposition unreadPart(OnTheWay.Why why, boolean fixed) {
        return new Proposition.Unread(where, unread++, why, fixed, true);
    }
}
