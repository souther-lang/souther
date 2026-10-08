package souther.compiler.partition;

import souther.compiler.check.AffineForms;
import souther.compiler.check.BooleanMeaning;
import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.Choice;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.ElementWitness;
import souther.compiler.check.Location;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.StatedComparison;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputNumber;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.InputTruth;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Conclusion;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.BuiltFrom;
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
 * <p><b>Each step is a {@link Derivation}.</b> What is built here is how the condition was read, a
 * rule at a time; what it states is what that concludes, worked out once at the end. So nothing here
 * writes a proposition, and a step that is no rule of the set has nowhere to be written.
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
     * What a condition states, how that was derived, and the parts it was read from.
     *
     * @param proposition what holds where the condition does
     * @param derivation  how it was read, a rule at a time
     * @param leaves      every part met, in the order met — a part met twice is here twice
     */
    record Pulled(Proposition proposition, Derivation derivation, List<Leaf> leaves) {

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

    /** A step a part was read at, and the expression it was read off. */
    private record Met(Derivation step, Denotation from) {}

    private final InputReading read;
    private final Optional<ModelOccurrence> where;
    private final List<Met> met = new ArrayList<>();
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
        return reading.pulled(reading.observe(truth, AnswerAspect.TRUTH, reads));
    }

    /**
     * What a comparison the source wrote states, read as any truth is: a size held where it parts
     * nought from every size above it is whether the container holds anything.
     */
    static Pulled ofAComparison(StatedComparison comparison, InputReads reads, InputReading read,
                                Optional<ModelOccurrence> where) {
        Pullback reading = new Pullback(read, where);
        AnEmptinessCheck.Checked checked = AnEmptinessCheck.checked(comparison);
        Derivation stated = checked != null
                ? new Derivation.AnEmptinessCheck(
                        reading.observe(checked.container(), AnswerAspect.EMPTINESS, reads),
                        checked.emptyWhereItHolds())
                : reading.compared(comparison, false, reads);
        return reading.pulled(stated);
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
        return reading.pulled(reading.observe(container, AnswerAspect.EMPTINESS, reads));
    }

    /** What {@code stated} concludes, with every part met as what it came to. */
    private Pulled pulled(Derivation stated) {
        Conclusion conclusion = new Conclusion(where);
        Proposition proposition = conclusion.of(stated);
        List<Leaf> leaves = new ArrayList<>();
        for (Met each : met) {
            Proposition part = each.step() instanceof Derivation.AMembership membership
                    ? membership.sameValue() : conclusion.concludedAt(each.step());
            if (part != null && !(part instanceof Proposition.Always)) {
                leaves.add(new Leaf(part, each.from()));
            }
        }
        return new Pulled(proposition, stated, List.copyOf(leaves));
    }

    /**
     * How {@code e} coming out on {@code aspect} was read: holding, holding something, holding a
     * value.
     */
    private Derivation observe(Core standing, AnswerAspect aspect, InputReads reads) {
        Core e = Core.withoutStanding(standing);
        switch (e) {
            case Core.LetIn let -> {
                return new Derivation.ThroughABinding(
                        observe(let.body(), aspect, reads.and(let.binder(), let.value())));
            }
            case Core.Read name when reads.meaningOf(name, read.rules().symbols(),
                    read.rules().newtypes()) instanceof ReadMeaning.Through through -> {
                return new Derivation.ThroughABinding(
                        observe(through.denotes().value(), aspect, through.denotes().at()));
            }
            case Core.If iff -> {
                Derivation cond = observe(iff.cond(), AnswerAspect.TRUTH, reads);
                Derivation then = observe(iff.then(), aspect, reads);
                return new Derivation.IfThenElse(cond, then, observe(iff.els(), aspect, reads));
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

    /**
     * How a truth that is no binding, name or choice was read, by the first rule in this order that
     * reads all of it — or, where none does, the first that takes it at all.
     */
    private Derivation truth(Core standing, InputReads reads) {
        Core e = Core.withoutStanding(standing);
        AnOperationApplied applied = AnOperationApplied.of(e);
        Derivation taken = firstThatReadsIt(List.of(
                () -> writtenOut(e, AnswerAspect.TRUTH),
                () -> BooleanMeaning.underADenial(e, true).<Derivation>map(denied ->
                        new Derivation.UnderADenial(
                                observe(denied.part(), AnswerAspect.TRUTH, reads),
                                !denied.positive())).orElse(null),
                () -> BooleanMeaning.folded(e, read.rules().symbols())
                        .<Derivation>map(Derivation.Folded::new).orElse(null),
                () -> joined(e, reads),
                () -> {
                    TermPath position = InputTruth.positionOf(e, reads, read.rules().newtypes());
                    return position == null ? null
                            : leaf(new Derivation.ATruthAtAPosition(position, true), e, reads);
                },
                () -> BooleanMeaning.asAComparison(e).map(stated -> comparison(stated, e, reads))
                        .orElse(null),
                () -> applied == null ? null : witnessed(applied, e, AnswerAspect.TRUTH, reads),
                () -> applied == null ? null : membership(applied, e, reads)));
        return taken != null ? taken : unread(e, reads, unreadAs(applied, AnswerAspect.TRUTH));
    }

    /**
     * What a value the source wrote out answers about {@code aspect}, or null where {@code standing}
     * is no such value.
     */
    private static Derivation writtenOut(Core standing, AnswerAspect aspect) {
        Core e = Core.withoutStanding(standing);
        return switch (aspect) {
            case TRUTH -> e instanceof Core.Bool written
                    ? new Derivation.WrittenOut(written.value()) : null;
            case EMPTINESS -> switch (e) {
                case Core.ListLit list -> new Derivation.WrittenOut(!list.elements().isEmpty());
                case Core.Str text -> new Derivation.WrittenOut(!text.value().isEmpty());
                default -> null;
            };
            case PRESENCE -> switch (e) {
                case Core.OptionSome _ -> new Derivation.WrittenOut(true);
                case Core.OptionNone _ -> new Derivation.WrittenOut(false);
                default -> null;
            };
        };
    }

    /** Two truths joined by a connective, or null where {@code standing} joins none. */
    private Derivation joined(Core standing, InputReads reads) {
        if (!(Core.withoutStanding(standing) instanceof Core.Binary binary)) {
            return null;
        }
        return ConditionJoin.of(binary.op()).<Derivation>map(join -> {
            Derivation left = observe(binary.left(), AnswerAspect.TRUTH, reads);
            return new Derivation.Joined(join.under(true), left,
                    observe(binary.right(), AnswerAspect.TRUTH, reads));
        }).orElse(null);
    }

    /** A comparison the source wrote: whether a container holds anything, or the relation. */
    private Derivation comparison(StatedComparison stated, Core e, InputReads reads) {
        AnEmptinessCheck.Checked checked = AnEmptinessCheck.checked(stated);
        if (checked != null) {
            Derivation some = asking(new Denotation(e, reads),
                    () -> observe(checked.container(), AnswerAspect.EMPTINESS, reads));
            return new Derivation.AnEmptinessCheck(some, checked.emptyWhereItHolds());
        }
        return leaf(compared(stated, fixed(e, reads), reads), e, reads);
    }

    /**
     * How a container that is no binding, name or choice holding something was read, chosen as
     * {@link #truth} chooses.
     */
    private Derivation holdingSomething(Core standing, InputReads reads) {
        Core e = Core.withoutStanding(standing);
        AnOperationApplied applied = AnOperationApplied.of(e);
        // What the container's holding anything is read off, or where reading it stopped, is the
        // question that asked it, where something asked it.
        Denotation asked = askedAt != null ? askedAt : new Denotation(e, reads);
        Derivation taken = firstThatReadsIt(List.of(
                () -> writtenOut(e, AnswerAspect.EMPTINESS),
                () -> applied == null ? null
                        : witnessed(applied, e, AnswerAspect.EMPTINESS, reads),
                () -> applied == null ? null : kept(applied, reads),
                () -> {
                    if (!(reads.pathOf(e, read.rules().newtypes())
                            instanceof PathResolution.At(TermPath held))) {
                        return null;
                    }
                    Derivation some = holdsSomethingAt(held);
                    return leaf(some != null ? some : new Derivation.Stopped(
                            new WhyUnread.NoMeasureOfItsSize(), fixed(e, reads)), asked);
                }));
        return taken != null ? taken : leaf(new Derivation.Stopped(
                unreadAs(applied, AnswerAspect.EMPTINESS), fixed(e, reads)), asked);
    }

    /** What {@code applied} was handed, where it holds something exactly where that does. */
    private Derivation kept(AnOperationApplied applied, InputReads reads) {
        DeclaredArgument kept = DefaultBoundOperationFacts.get()
                .keepsWhetherItHoldsAnything(applied.operation());
        Core source = kept == null ? null : applied.argument(kept);
        if (source == null || !(applied.operation() instanceof ValueName.Stdlib operation)) {
            return null;
        }
        return new Derivation.KeepsWhetherItHoldsAnything(operation,
                observe(source, AnswerAspect.EMPTINESS, reads));
    }

    /**
     * How an optional that is no binding, name or choice holding a value was read, chosen as
     * {@link #truth} chooses.
     */
    private Derivation present(Core standing, InputReads reads) {
        Core e = Core.withoutStanding(standing);
        AnOperationApplied applied = AnOperationApplied.of(e);
        Derivation taken = firstThatReadsIt(List.of(
                () -> writtenOut(e, AnswerAspect.PRESENCE),
                () -> applied == null ? null
                        : witnessed(applied, e, AnswerAspect.PRESENCE, reads),
                () -> reads.pathOf(e, read.rules().newtypes()) instanceof PathResolution.At(
                        TermPath at)
                        ? leaf(new Derivation.PresentAtAPosition(at), e, reads) : null));
        return taken != null ? taken : unread(e, reads, unreadAs(applied, AnswerAspect.PRESENCE));
    }

    /** The one of {@code rules} an expression is read by ({@link RuleChoice}). */
    private Derivation firstThatReadsIt(List<Supplier<Derivation>> rules) {
        return RuleChoice.firstThatReadsIt(rules, met);
    }

    /**
     * How a match answering {@code aspect} was read: some arm taken, and what that arm answers.
     *
     * <p>An arm is taken where the value is one of its cases and none of an arm before it. Which
     * cases a value written in the source is is settled before any row ({@link
     * InputReads#whetherEveryRowTakes}); one at a position is a case the row writes there.
     */
    private Derivation ofAMatch(Core.Match match, AnswerAspect aspect, InputReads reads) {
        Set<TypeSymbol> written = reads.casesWritten(match.scrutinee(),
                read.rules().symbols(), read.rules().newtypes());
        TermPath subject = reads.pathOf(match.scrutinee(), read.rules().newtypes())
                instanceof PathResolution.At(TermPath at) ? at : null;
        List<Derivation.MatchArms.Arm> arms = new ArrayList<>();
        for (Core.Case arm : match.cases()) {
            Derivation selects;
            Optional<Boolean> every = InputReads.whetherEveryRowTakes(arm, written);
            if (every.isPresent()) {
                selects = new Derivation.CasesWrittenOut(every.get());
            } else if (arm.pattern() == null) {
                selects = new Derivation.CasesWrittenOut(true);
            } else if (subject != null) {
                selects = new Derivation.CasesAtAPosition(subject,
                        CasesLeft.selectedBy(arm.pattern()));
            } else {
                // Which arm is taken is the match's own reader's to classify, and no part offered
                // here: what is read is what the arms answer. Not the same whatever the input even
                // over values the source wrote out, since what is matched is one of several of them
                // and each may take another arm — one alone is settled above.
                selects = new Derivation.Stopped(
                        new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SCRUTINEE), false);
            }
            InputReads inside = reads.choosing(Choice.Decides.ofCase(match, arm),
                    read.rules().symbols(), read.rules().newtypes());
            arms.add(new Derivation.MatchArms.Arm(selects, observe(arm.body(), aspect, inside)));
        }
        return new Derivation.MatchArms(arms);
    }

    /**
     * How {@code applied} coming out on {@code aspect} was read where the library declares the
     * element that witnesses it — or null where it declares none on that side.
     */
    private Derivation witnessed(AnOperationApplied applied, Core e, AnswerAspect aspect,
                                 InputReads reads) {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        ElementWitness law = facts.resultHasAnElementWitness(applied.operation());
        if (law == null || law.result().aspect() != aspect
                || !(applied.operation() instanceof ValueName.Stdlib operation)) {
            return null;
        }
        Core over = applied.argument(law.container());
        Core handed = applied.argument(law.closure());
        if (over == null || handed == null) {
            return null;
        }
        return new Derivation.AWitnessLaw(operation, law.result(),
                someElement(over, handed, law.ofTheClosure(), e, reads));
    }

    /**
     * How some element of {@code over}, handed to the closure at {@code handed}, making it answer
     * as {@code witness} was read.
     */
    private Derivation someElement(Core over, Core handed, SideAnswered witness, Core e,
                                   InputReads reads) {
        Denotation closure = reads.denotes(handed, read.rules().symbols(), read.rules().newtypes());
        if (!(Core.withoutStanding(closure.value()) instanceof Core.Block block)) {
            return unread(e, reads,
                    new WhyUnread.NotYetComposed(WhyUnread.NotYetComposed.Step.A_CLOSURE_BY_NAME));
        }
        Denotation container = reads.standing(over, read.rules().symbols(),
                read.rules().newtypes());
        // A container the source wrote out has no element where it is empty. Otherwise what the
        // closure is handed is one of the written values, which is how the reading of the input
        // reads its parameter ({@code ReadMeaning.OneOf}) for every reader of the closure: what it
        // states of the input is what it states of any of them.
        if (Core.withoutStanding(container.value()) instanceof Core.ListLit list) {
            return new Derivation.OverElementsWrittenOut(list.elements().isEmpty()
                    ? Optional.empty()
                    : Optional.of(observe(block.body(), witness.aspect(), closure.at())),
                    witness.holds());
        }
        if (!(reads.pathOf(over, read.rules().newtypes()) instanceof PathResolution.At(
                TermPath held))) {
            return unread(over, reads,
                    new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.CONTAINER));
        }
        // The element is what stands at the container's element inside the closure, so the same
        // container quantified inside itself would name two elements one subject.
        if (!quantifying.add(held)) {
            return unread(e, reads, new WhyUnread.TwoElementsOfOneContainer());
        }
        Derivation answered;
        try {
            answered = observe(block.body(), witness.aspect(), closure.at());
        } finally {
            quantifying.remove(held);
        }
        Proposition element = new Conclusion(where).of(answered);
        boolean asked = Derivation.SomeElementMeeting.asksWhetherItHoldsAnything(held,
                witness.holds() ? element : element.denied());
        Optional<Derivation> holdsSomething = Optional.empty();
        if (asked) {
            Derivation some = holdsSomethingAt(held);
            holdsSomething = Optional.of(some != null
                    ? leaf(some, askedAt != null ? askedAt : new Denotation(e, reads))
                    : unread(over, reads, new WhyUnread.NoMeasureOfItsSize()));
        }
        return new Derivation.SomeElementMeeting(held, answered, witness.holds(), holdsSomething);
    }

    /**
     * How a container holding the value {@code applied} asks about was read: some element the same
     * as it — or null where {@code applied} asks no such thing.
     */
    private Derivation membership(AnOperationApplied applied, Core e, InputReads reads) {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        DeclaredArgument asked = facts.asksWhetherItsContainerHolds(applied.operation());
        var reads0 = facts.readsItsContainer(applied.operation());
        if (asked == null || reads0 == null
                || !(applied.operation() instanceof ValueName.Stdlib operation)) {
            return null;
        }
        Core over = applied.argument(reads0.container());
        if (!(reads.pathOf(over, read.rules().newtypes()) instanceof PathResolution.At(
                TermPath held))) {
            return unread(over, reads,
                    new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.CONTAINER));
        }
        if (!(reads.pathOf(applied.argument(asked), read.rules().newtypes())
                instanceof PathResolution.At(TermPath value))) {
            return unread(e, reads, new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.VALUE));
        }
        return leaf(new Derivation.AMembership(operation, held, value), e, reads);
    }

    /** That the container at {@code held} holds something, as its size above nought — or null
     *  where its size is no term of this input. */
    private Derivation holdsSomethingAt(TermPath held) {
        Type container = read.domain().typeAt(held, read.rules());
        ValueName.Stdlib size = container == null ? null
                : NumericMeasures.takenOf(container, read.rules().inners());
        NumericTerm.TakenOf count = size == null ? null : NumericTerm.TakenOf.of(size, held,
                container, read.rules().inners(), read.rules().symbols());
        return count == null ? null : new Derivation.SizeAboveNought(count);
    }

    /**
     * A comparison the arithmetic of the input did not read to a line, read as a relation over the
     * quantities a condition is read over: numbers of the input, and numbers of values the body
     * bound — or unread where some part of it is neither.
     *
     * <p>Asked where what a value is computed from is unknown: a dependency's answer, what an attempt
     * built. Which value it is is still known, by the binding that names it, and two comparisons over
     * one name are about one number. The arithmetic is {@link AffineForms}'s, the one walk every
     * reader of a number in this compiler composes by; this says only what its atoms are.
     */
    private Derivation ofBoundValues(StatedComparison comparison, boolean fixed,
                                     InputReads reads) {
        // A comparison whose answer is the same on every run is no relation between numbers that
        // vary: what it compares can be a parameter of a closure applied to elements written out,
        // and that name stands for a different value each time it is applied.
        if (fixed) {
            return new Derivation.Stopped(new WhyUnread.NotYetComposed(
                    WhyUnread.NotYetComposed.Step.VALUES_WRITTEN_OUT), true);
        }
        List<LinearForm<Quantity>> sides = new ArrayList<>();
        for (Core side : List.of(comparison.left(), comparison.right())) {
            switch (AffineForms.outcome(side, reads, quantities())) {
                case AffineForms.Outcome.Composed<Quantity, InputReads>(var form) -> sides.add(form);
                case AffineForms.Outcome.StoppedAt<Quantity, InputReads>(var node, var at) -> {
                    return new Derivation.Stopped(noFormOf(node, at), false);
                }
            }
        }
        LinearForm<Quantity> form = sides.get(0).minus(sides.get(1)).orNull();
        Rel states = comparison.claim().statedRelation();
        if (form == null) {
            return new Derivation.Stopped(new WhyUnread.OutsideTheLinearFragment(), false);
        }
        if (form.coefs().isEmpty()) {
            return new Derivation.ACutThatCutsNothing(states.holds(form.constant().signum()));
        }
        Rel proposition = states.orItsDenial();
        return new Derivation.AComparisonRead(Derivation.ComparisonReading.OVER_BOUND_VALUES,
                new Relation.Affine(form, proposition), states == proposition);
    }

    /**
     * What this reading calls an atom of a number: a number of the input where the expression is
     * one, and otherwise a number of a value the body bound, named by its binding and the fields
     * read off it.
     *
     * <p>A name is one value only where it is one on a run. A name handed each element of a
     * container, or one that can be any of several values, stands for a different value each time
     * it is read, so a relation over it relates nothing and it is no atom.
     */
    private AffineForms.Reading<Quantity, InputReads> quantities() {
        return new AffineForms.Reading<>() {

            @Override
            public Symbols symbols() {
                return read.rules().symbols();
            }

            @Override
            public DeclarationAccess declarations() {
                return read.rules().declarations();
            }

            @Override
            public LinearForm<Quantity> leafOf(Core node, InputReads at) {
                NumericTerm term = InputNumber.of(node, read.domain(), at, read.rules());
                if (term != null) {
                    return LinearForm.atom(new DecisionAtom.OfTheInput(term));
                }
                List<TermPath.Step> steps = new ArrayList<>();
                Core under = Core.withoutStanding(node);
                while (true) {
                    if (under instanceof Core.FieldProjection projection) {
                        under = Core.withoutStanding(projection.lastAccess());
                    } else if (under instanceof Core.FieldAccess access) {
                        if (Location.isStep(access.target().type(), access.field(),
                                read.rules().newtypes())) {
                            steps.addFirst(new TermPath.Step.Field(access.field()));
                        }
                        under = Core.withoutStanding(access.target());
                    } else {
                        break;
                    }
                }
                if (!(under instanceof Core.Read name)) {
                    return null;
                }
                return switch (at.meaningOf(name, read.rules().symbols(), read.rules().newtypes())) {
                    case ReadMeaning.Element _, ReadMeaning.OneOf _, ReadMeaning.Position _ -> null;
                    case ReadMeaning.Through _, ReadMeaning.Unknown _ -> LinearForm.atom(
                            new Quantity.OfABinding(name.binding(), steps, node.type()));
                };
            }

            @Override
            public InputReads inside(Core.LetIn li, InputReads at) {
                return at.and(li.binder(), li.value());
            }

            @Override
            public AffineForms.ReadThrough<InputReads> readThrough(Core.Read name, InputReads at) {
                return NameAnswers.denoting(name, at, read.rules().symbols(),
                        read.rules().newtypes());
            }

            @Override
            public List<AffineForms.ReadThrough<InputReads>> alternativesOf(Core.Read name,
                                                                           InputReads at) {
                return NameAnswers.alternativesOf(name, at, read.rules().symbols(),
                        read.rules().newtypes());
            }

            @Override
            public boolean readsThrough(Core.FieldAccess fa, InputReads at) {
                // A field of a value that stands nowhere is arithmetic's to walk into, as it is for
                // the reading of the input's own numbers ({@link AffineReading}).
                boolean stands = !(at.pathOf(fa.target(), read.rules().newtypes())
                        instanceof PathResolution.NotAPosition);
                return !stands && !Location.isStep(fa.target().type(), fa.field(),
                        read.rules().newtypes());
            }
        };
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
    private Derivation compared(StatedComparison comparison, boolean fixed, InputReads reads) {
        InputTruth truth = InputTruth.compared(comparison, true, reads, read.rules().symbols(),
                read.rules().newtypes());
        if (truth != null) {
            return new Derivation.ATruthCompared(truth.at(), truth.held());
        }
        return switch (AffineReading.read(comparison, read.domain(), reads, read.rules())) {
            case AffineReading.OfAComparison.Cuts(var affine) -> {
                Rel states = affine.claim().statedRelation();
                LinearForm<NumericTerm> against =
                        affine.form().minus(LinearForm.constant(affine.cut())).orNull();
                if (against == null) {
                    yield new Derivation.Stopped(new WhyUnread.OutsideTheLinearFragment(), fixed);
                }
                Rel proposition = states.orItsDenial();
                yield new Derivation.AComparisonRead(Derivation.ComparisonReading.AS_A_CUT,
                        new Relation.Affine(
                                asQuantities(DecisionComparison.ofTheInput(against)), proposition),
                        states == proposition);
            }
            case AffineReading.OfAComparison.CutsNothing constant ->
                    new Derivation.ACutThatCutsNothing(
                            constant.holds(comparison.claim().statedRelation()));
            case AffineReading.OfAComparison.NotHeld _ -> ofBoundValues(comparison, fixed, reads);
            case AffineReading.OfAComparison.Stopped _ -> {
                ComparedLine drawn = ComparedLine.asWritten(comparison, read, reads);
                if (drawn == null) {
                    yield ofBoundValues(comparison, fixed, reads);
                }
                Rel states = drawn.claim().statedRelation();
                Rel proposition = states.orItsDenial();
                yield new Derivation.AComparisonRead(Derivation.ComparisonReading.ON_AN_ORDER,
                        new Relation.Ordered(new DecisionAtom.OfTheInput(drawn.term()),
                                drawn.value(), proposition),
                        states == proposition);
            }
        };
    }

    /** {@code step}, kept as a part met at the expression it was read off. */
    private Derivation leaf(Derivation step, Core from, InputReads reads) {
        return leaf(step, new Denotation(from, reads));
    }

    private Derivation leaf(Derivation step, Denotation from) {
        met.add(new Met(step, from));
        return step;
    }

    /** {@code reading}, with whether a container holds anything asked at {@code where}. */
    private Derivation asking(Denotation where, Supplier<Derivation> reading) {
        Denotation outer = askedAt;
        askedAt = where;
        try {
            return reading.get();
        } finally {
            askedAt = outer;
        }
    }

    /** {@code e}, which nothing here reads the meaning of. */
    private Derivation unread(Core e, InputReads reads, WhyUnread why) {
        return leaf(new Derivation.Stopped(why, fixed(e, reads)), e, reads);
    }

    /**
     * Why {@code applied} — or, where nothing is applied, the value it is asked of — coming out on
     * {@code aspect} was read as nothing, once no rule took it.
     */
    private static WhyUnread unreadAs(AnOperationApplied applied, AnswerAspect aspect) {
        if (applied == null) {
            return new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT);
        }
        return switch (applied.operation()) {
            case ValueName.Stdlib operation -> new WhyUnread.NoLawFor(operation, aspect);
            case ValueName.Behavior _ -> aspect == AnswerAspect.EMPTINESS
                    ? new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT)
                    : new WhyUnread.NotYetComposed(
                            WhyUnread.NotYetComposed.Step.A_DEPENDENCYS_ANSWER);
            case ValueName.Helper _ -> new WhyUnread.WhatARecursiveHelperAnswers();
            default -> new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT);
        };
    }

    /**
     * Why the arithmetic stopped at {@code stopped}, read in {@code reads}: what stands at the end of
     * the accesses it is made of.
     *
     * <p>Said of the expression {@link AffineForms} could not compose and named no atom for, which is
     * the most particular one; the walk is what knows the arithmetic, so what it stopped at is no
     * form whatever this would say of it.
     */
    private WhyUnread noFormOf(Core stopped, InputReads reads) {
        Core e = Core.withoutStanding(stopped);
        while (true) {
            if (e instanceof Core.FieldProjection projection) {
                e = Core.withoutStanding(projection.lastAccess());
            } else if (e instanceof Core.FieldAccess access) {
                e = Core.withoutStanding(access.target());
            } else {
                break;
            }
        }
        if (e instanceof Core.Read name) {
            return switch (reads.meaningOf(name, read.rules().symbols(), read.rules().newtypes())) {
                case ReadMeaning.Element _ ->
                        new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.CONTAINER);
                case ReadMeaning.OneOf _ -> new WhyUnread.NotYetComposed(
                        WhyUnread.NotYetComposed.Step.VALUES_WRITTEN_OUT);
                case ReadMeaning.Unknown _, ReadMeaning.Position _, ReadMeaning.Through _ ->
                        new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT);
            };
        }
        switch (e) {
            // Arithmetic the walk has a rule for and could not compose: a product of two values
            // neither of which is written out, a quotient by one that is not.
            case Core.Binary _, Core.Neg _ -> {
                return new WhyUnread.OutsideTheLinearFragment();
            }
            // A choice between values, where what is chosen is one of the arms.
            case Core.If _, Core.IfConstructed _, Core.Match _ -> {
                return new WhyUnread.NotYetComposed(
                        WhyUnread.NotYetComposed.Step.A_CHOICE_BY_CASES);
            }
            default -> { }
        }
        AnOperationApplied applied = AnOperationApplied.of(e);
        if (applied == null) {
            return new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT);
        }
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        return switch (applied.operation()) {
            case ValueName.Behavior _ -> new WhyUnread.NotYetComposed(
                    WhyUnread.NotYetComposed.Step.A_DEPENDENCYS_ANSWER);
            case ValueName.Helper _ -> new WhyUnread.WhatARecursiveHelperAnswers();
            case ValueName.Stdlib operation -> {
                if (facts.statesTheOrderOfItsArguments().contains(operation)) {
                    yield new WhyUnread.NotYetComposed(
                            WhyUnread.NotYetComposed.Step.AN_ORDER_OF_ITS_ARGUMENTS);
                }
                if (!facts.isDefinedByCases(operation).isEmpty()) {
                    yield new WhyUnread.NotYetComposed(
                            WhyUnread.NotYetComposed.Step.A_CHOICE_BY_CASES);
                }
                if (facts.takenAs(operation) != null && !applied.args().isEmpty()) {
                    yield noNumberOf(operation, applied.args().getFirst(), reads);
                }
                yield new WhyUnread.NoFormOfWhatItAnswers(operation);
            }
            default -> new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT);
        };
    }

    /**
     * Why a number {@code measure} takes of {@code measured} is no number of the input: what stands
     * there is no position, and what made it says nothing of that number in terms of what it was
     * handed — or does, by a step not taken yet.
     */
    private WhyUnread noNumberOf(ValueName.Stdlib measure, Core measured, InputReads reads) {
        Core made = Core.withoutStanding(reads.standing(measured, read.rules().symbols(),
                read.rules().newtypes()).value());
        if (!(AnOperationApplied.of(made) instanceof AnOperationApplied applied
                && applied.operation() instanceof ValueName.Stdlib madeBy)) {
            return new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT);
        }
        // As many as what it was handed, so its size is that one's.
        BuiltFrom<DeclaredArgument> built = DefaultBoundOperationFacts.get()
                .buildsItsResultFrom(madeBy);
        if (built != null && built.mapsEachElementOf() != null) {
            return new WhyUnread.NotYetComposed(
                    WhyUnread.NotYetComposed.Step.A_SIZE_AN_OPERATION_KEEPS);
        }
        return new WhyUnread.ANumberOfWhatAnOperationAnswers(measure, madeBy);
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
}
