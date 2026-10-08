package souther.compiler.partition;

import souther.compiler.check.AffineForms;
import souther.compiler.check.AnOperationApplied;
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
import souther.compiler.check.TheSignOfAnOrder;
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
import souther.compiler.meaning.MeaningsOfABody.Meaning;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.UnheldNumber;
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
     * @param meaning what holds where the condition does, and how it was read a rule at a time
     * @param leaves  every part met, in the order met — a part met twice is here twice
     */
    record Pulled(Meaning meaning, List<Leaf> leaves) {

        /** What holds where the condition does. */
        Proposition proposition() {
            return meaning.states();
        }

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
            partsOf(proposition(), parts);
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
    /** What the candidates for each expression state, concluded once a step ({@link RuleChoice}). */
    private final Conclusion trying = Conclusion.reusing();
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
        return reading.pulled(reading.comparison(comparison, null, false, reads));
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
        if (!mayBeCarriedPast(comparison)) {
            return false;
        }
        Pulled pulled = ofAComparison(comparison, reads, read, Optional.empty());
        return !(pulled.proposition() instanceof Proposition.Compared)
                && pulled.turnsOn().stream()
                        .noneMatch(leaf -> leaf.part() instanceof Proposition.Unread);
    }

    /**
     * Whether {@code comparison} is one {@link #carriesPast} can answer yes for, which is a question
     * about its shape alone: only an emptiness check is carried anywhere.
     */
    static boolean mayBeCarriedPast(StatedComparison comparison) {
        return AnEmptinessCheck.checked(comparison) != null;
    }

    /** What {@code container} holding something states. */
    static Pulled ofHoldingSomething(Core container, InputReads reads, InputReading read,
                                     Optional<ModelOccurrence> where) {
        Pullback reading = new Pullback(read, where);
        return reading.pulled(reading.observe(container, AnswerAspect.EMPTINESS, reads));
    }

    /**
     * What {@code stated} concludes, with every part met as what it came to.
     *
     * <p>A part is a step of {@code stated}: one this concluding reached. A step met by a rule that
     * was not kept is in no derivation concluded here, so whatever was met on the way, the parts
     * are the derivation's own.
     */
    private Pulled pulled(Derivation stated) {
        Conclusion conclusion = new Conclusion(where);
        Meaning meaning = conclusion.meaningOf(stated);
        List<Leaf> leaves = new ArrayList<>();
        for (Met each : met) {
            Proposition concluded = conclusion.concludedAt(each.step());
            if (concluded == null) {
                continue;
            }
            Proposition part = each.step() instanceof Derivation.AMembership membership
                    ? membership.sameValue() : concluded;
            if (!(part instanceof Proposition.Always)) {
                leaves.add(new Leaf(part, each.from()));
            }
        }
        return new Pulled(meaning, List.copyOf(leaves));
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
                () -> BooleanMeaning.asAComparison(e).map(stated -> comparison(stated,
                        new Denotation(e, reads), fixed(e, reads), reads)).orElse(null),
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

    /**
     * How a comparison the source wrote was read, by the first of the rules for one that reads all
     * of it ({@link RuleChoice}).
     *
     * <p>A size held where it parts nought from every size above it is whether the container holds
     * anything; and every comparison is the relation it states — about a truth of the input, as a
     * cut on the input's arithmetic, as a line on an order that arithmetic does not count, or over
     * values the body bound — and a comparison of the sign an operation answers the order of its
     * arguments by is the comparison of those arguments, read by the same rules. More than one of
     * them takes some comparisons, and the one tried first is not the one kept where it leaves a
     * part unread and one after it reads all of it.
     *
     * @param at    where the comparison is a part of a larger condition, kept as a part met there;
     *              null where the comparison is itself what is read
     * @param fixed whether its answer is the same on every run
     */
    private Derivation comparison(StatedComparison stated, Denotation at, boolean fixed,
                                  InputReads reads) {
        return firstThatReadsIt(rulesFor(stated, at, fixed, reads));
    }

    /** The rules that take a comparison the source wrote, in the order they are tried. */
    private List<Supplier<Derivation>> rulesFor(StatedComparison stated, Denotation at,
                                                boolean fixed, InputReads reads) {
        AnEmptinessCheck.Checked checked = AnEmptinessCheck.checked(stated);
        Once<AffineReading.OfAComparison> arithmetic = new Once<>(
                () -> AffineReading.read(stated, read.domain(), reads, read.rules()));
        return List.of(
                () -> checked == null ? null : new Derivation.AnEmptinessCheck(at == null
                        ? observe(checked.container(), AnswerAspect.EMPTINESS, reads)
                        : asking(at, () -> observe(checked.container(), AnswerAspect.EMPTINESS,
                                reads)), checked.emptyWhereItHolds()),
                () -> partOf(at, truthCompared(stated, reads)),
                () -> partOf(at, asACut(stated, arithmetic.get(), fixed)),
                () -> partOf(at, onAnOrder(stated, arithmetic.get(), reads)),
                () -> partOf(at, ofItsArguments(stated, fixed, reads)),
                () -> partOf(at, ofBoundValues(stated, fixed, reads)));
    }

    /**
     * What each rule that takes {@code comparison} concludes, each read on its own and in the order
     * they are tried; a rule that does not take it is left out.
     *
     * <p>For holding the rules to one another: two of them that read all of one comparison have to
     * state one thing, or which was tried first would decide what the model says.
     */
    static List<Proposition> byEachRule(StatedComparison comparison, InputReads reads,
                                        InputReading read) {
        int rules = new Pullback(read, Optional.empty())
                .rulesFor(comparison, null, false, reads).size();
        List<Proposition> out = new ArrayList<>();
        for (int i = 0; i < rules; i++) {
            Pullback alone = new Pullback(read, Optional.empty());
            Derivation taken = alone.rulesFor(comparison, null, false, reads).get(i).get();
            if (taken != null) {
                out.add(alone.pulled(taken).proposition());
            }
        }
        return out;
    }

    /** {@code step}, kept as a part met at {@code at} where there is one. */
    private Derivation partOf(Denotation at, Derivation step) {
        return step == null || at == null ? step : leaf(step, at);
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
        return RuleChoice.firstThatReadsIt(rules, met, trying);
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
        Proposition element = trying.of(answered);
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
     * A comparison read as a relation over the quantities a condition is read over: numbers of the
     * input, and numbers of values the body bound — or unread where some part of it is neither.
     *
     * <p>The last rule for a comparison, and the one that takes every comparison: what reads the
     * input alone is tried before it. It reads what those cannot, where what a value is computed
     * from is unknown: a dependency's answer, what an attempt built. Which value it is is still known, by the binding that names it, and two comparisons over
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
                case AffineForms.Outcome.StoppedAt<Quantity, InputReads> stopped -> {
                    return new Derivation.Stopped(noFormOf(stopped), false);
                }
            }
        }
        LinearForm<Quantity> form;
        switch (sides.get(0).minus(sides.get(1))) {
            case ExactAnswer.Held<LinearForm<Quantity>>(LinearForm<Quantity> held) -> form = held;
            case ExactAnswer.Unheld<LinearForm<Quantity>>(UnheldNumber why) -> {
                return new Derivation.Stopped(new WhyUnread.ANumberNotHeld(why), false);
            }
        }
        Rel states = comparison.claim().statedRelation();
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
     * A comparison of a truth of the input against a truth written out, or null where it is no
     * such comparison.
     */
    private Derivation truthCompared(StatedComparison comparison, InputReads reads) {
        InputTruth truth = InputTruth.compared(comparison, true, reads, read.rules().symbols(),
                read.rules().newtypes());
        return truth == null ? null : new Derivation.ATruthCompared(truth.at(), truth.held());
    }

    /**
     * A comparison as the cut the arithmetic of the input reads it to, or as one that cuts nothing —
     * or null where that arithmetic read it to neither.
     *
     * <p>Off the same reading a border on it is drawn from everywhere a comparison is, so what it
     * states here is what a border on it is drawn at.
     */
    private static Derivation asACut(StatedComparison comparison,
                                     AffineReading.OfAComparison arithmetic, boolean fixed) {
        return switch (arithmetic) {
            case AffineReading.OfAComparison.Cuts(var affine) -> {
                Rel states = affine.claim().statedRelation();
                LinearForm<NumericTerm> against;
                switch (affine.form().minus(LinearForm.constant(affine.cut()))) {
                    case ExactAnswer.Held<LinearForm<NumericTerm>>(var held) -> against = held;
                    case ExactAnswer.Unheld<LinearForm<NumericTerm>>(UnheldNumber why) -> {
                        yield new Derivation.Stopped(new WhyUnread.ANumberNotHeld(why), fixed);
                    }
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
            case AffineReading.OfAComparison.NotHeld _, AffineReading.OfAComparison.Stopped _ ->
                    null;
        };
    }

    /**
     * A comparison as a line on an order the arithmetic of the input stopped at, or null where it
     * did not stop or no line is drawn on what it stopped at.
     *
     * <p>Only where it stopped: a date against a written date and a case of an enumeration are
     * values it does not count, and the comparison still states a line on their order. A comparison
     * the arithmetic read is that arithmetic's, which is the reading a border is drawn by.
     */
    private Derivation onAnOrder(StatedComparison comparison,
                                 AffineReading.OfAComparison arithmetic, InputReads reads) {
        if (!(arithmetic instanceof AffineReading.OfAComparison.Stopped)) {
            return null;
        }
        ComparedLine drawn = ComparedLine.asWritten(comparison, read, reads);
        if (drawn == null) {
            return null;
        }
        Rel states = drawn.claim().statedRelation();
        Rel proposition = states.orItsDenial();
        return new Derivation.AComparisonRead(Derivation.ComparisonReading.ON_AN_ORDER,
                new Relation.Ordered(new DecisionAtom.OfTheInput(drawn.term()), drawn.value(),
                        proposition),
                states == proposition);
    }

    /**
     * A comparison of the number an operation answering the order of its two arguments answered, as
     * the comparison of those two arguments it states — or null where neither side is such a number,
     * or the other side is no number the same on every run.
     *
     * <p>What it states of them is {@link TheSignOfAnOrder}'s answer, the one the check reads such a
     * comparison by; what is this reading's own is the environment ({@link #sides}). The arguments
     * are read where the operation was applied, which is not where the comparison stands when a
     * name was given the answer, and by the rules for a comparison, as any comparison is: over the
     * input, on an order, or over values the body bound.
     */
    private Derivation ofItsArguments(StatedComparison comparison, boolean fixed,
                                      InputReads reads) {
        return switch (TheSignOfAnOrder.read(comparison, reads, sides())) {
            case null -> null;
            // What the comparison means, so only where the order of the two is all it states: one
            // that only proves an order is a rule about the number, which is no order's to read.
            case TheSignOfAnOrder.Read.OfTheArguments<InputReads> ordered
                    when !ordered.isTheCondition() -> null;
            case TheSignOfAnOrder.Read.OfTheArguments<InputReads> ordered
                    when ordered.operation() instanceof ValueName.Stdlib operation ->
                    new Derivation.AnOrderOfItsArguments(operation, firstThatReadsIt(
                            rulesFor(ordered.arguments(), null, fixed, ordered.at())));
            case TheSignOfAnOrder.Read.Settled<InputReads> settled
                    when settled.operation() instanceof ValueName.Stdlib operation ->
                    new Derivation.ASignItsBoundsSettle(operation, settled.holds());
            // An order the library declares is of one of its own operations.
            case TheSignOfAnOrder.Read.OfTheArguments<InputReads> _,
                 TheSignOfAnOrder.Read.Settled<InputReads> _ -> null;
        };
    }

    /**
     * What this reading answers about its environment for a comparison of a sign: a name is what
     * it stands for where it was given it, and the number against the sign is read as any number
     * here is ({@link #quantities}).
     */
    private TheSignOfAnOrder.Sides<InputReads> sides() {
        return new TheSignOfAnOrder.Sides<>() {

            @Override
            public AffineForms.ReadThrough<InputReads> standing(Core e, InputReads at) {
                Denotation stands = at.standing(e, read.rules().symbols(),
                        read.rules().newtypes());
                return new AffineForms.ReadThrough<>(stands.value(), stands.at());
            }

            @Override
            public ExactRatio constant(Core e, InputReads at) {
                return AffineForms.outcome(e, at, quantities())
                        instanceof AffineForms.Outcome.Composed<Quantity, InputReads>(
                                LinearForm<Quantity> number)
                        && number.coefs().isEmpty() ? number.constant() : null;
            }

            @Override
            public DeclarationAccess declarations() {
                return read.rules().declarations();
            }
        };
    }

    /** A value worked out by the first rule that asks for it, and not before or again. */
    private static final class Once<T> {

        private final Supplier<T> making;
        private T made;

        Once(Supplier<T> making) {
            this.making = making;
        }

        T get() {
            if (made == null) {
                made = making.get();
            }
            return made;
        }
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
     * Why the arithmetic stopped where it did, as a reason about the domain.
     *
     * <p>The arithmetic says why ({@link AffineForms.Halt}), and that is what this says, in these
     * words. Only where it had no rule for the expression is anything asked of the expression
     * itself, and then of what kind of value it is and not of how the arithmetic would have read it.
     */
    private WhyUnread noFormOf(AffineForms.Outcome.StoppedAt<Quantity, InputReads> stopped) {
        return switch (stopped.why()) {
            case AffineForms.Halt.NoRule<Quantity, InputReads> _ ->
                    noRuleFor(stopped.node(), stopped.at());
            case AffineForms.Halt.NotLinear<Quantity, InputReads> _ ->
                    new WhyUnread.OutsideTheLinearFragment();
            case AffineForms.Halt.NoNumberOnARun<Quantity, InputReads> _ ->
                    new WhyUnread.NoNumberOnARun();
            case AffineForms.Halt.NotHeld<Quantity, InputReads>(UnheldNumber why) ->
                    new WhyUnread.ANumberNotHeld(why);
            // Several values a name stands for, which only values written out are: a closure's
            // parameter applied to each of them.
            case AffineForms.Halt.ValuesDisagree<Quantity, InputReads> _ ->
                    new WhyUnread.NotYetComposed(WhyUnread.NotYetComposed.Step.VALUES_WRITTEN_OUT);
            case AffineForms.Halt.AnArgumentStopped<Quantity, InputReads>(var argument) ->
                    noFormOf(argument);
        };
    }

    /**
     * Why an expression the arithmetic has no rule for, read in {@code reads}, is no number of the
     * input: what stands at the end of the accesses it is made of.
     */
    private WhyUnread noRuleFor(Core stopped, InputReads reads) {
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
            // An operator that is no arithmetic: what it answers is no number of anything.
            case Core.Binary _ -> {
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
