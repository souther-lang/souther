package souther.compiler.partition;

import souther.compiler.check.AffineForms;
import souther.compiler.check.AnOperationApplied;
import souther.compiler.check.BooleanMeaning;
import souther.compiler.check.Carrier;
import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.Choice;
import souther.compiler.check.ClauseName;
import souther.compiler.check.ClausesInOrder;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DefaultBoundOperationFacts;
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
import souther.compiler.meaning.CasesOfAnAnswer;
import souther.compiler.meaning.Conclusion;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
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
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.TakenAs;
import souther.compiler.semantics.Unsayable;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;
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
 * An operation's answer comes out as its law says of its arguments ({@link OperationLaw}): a filter
 * holds something where some element was kept, a take where it was asked for some and handed some,
 * and how many a filter keeps is how many elements its closure holds of. What is left is a
 * comparison, a truth, a case or a value being there at a subject a row controls — the parts a
 * proposition is made of.
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
         *
         * <p>One expression stating one part is one part, however many times it was met: a closure
         * read on each of its applications meets the same comparison once on each, and an author
         * wrote it once.
         */
        List<Leaf> turnsOn() {
            Set<String> parts = new HashSet<>();
            partsOf(proposition(), parts);
            List<Leaf> out = new ArrayList<>();
            Map<Core, Set<String>> kept = new IdentityHashMap<>();
            for (Leaf leaf : leaves) {
                if (parts.contains(leaf.part().key()) && kept
                        .computeIfAbsent(leaf.from().value(), _ -> new HashSet<>())
                        .add(leaf.part().key())) {
                    out.add(leaf);
                }
            }
            return List.copyOf(out);
        }

        /** The spelling of each part {@code stated} turns on, either way round, into {@code into}. */
        private static void partsOf(Proposition stated, Set<String> into) {
            switch (stated) {
                case Proposition.Always _ -> { }
                case Proposition.Unread unread when unread.fixed() -> { }
                case Proposition.All all -> all.parts().forEach(part -> partsOf(part, into));
                case Proposition.Any any -> any.parts().forEach(part -> partsOf(part, into));
                case Proposition.OnAnApplication applications ->
                        applications.each().forEach(each -> partsOf(each, into));
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
    /**
     * What a value a row stands a dependency in for is, read as the decision table reads it: one
     * account of which answer a call is, so a column of the table and a part of what a condition
     * states are one subject.
     */
    private final DecisionSubjects subjects;
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
    /**
     * The counts of elements the comparison being read names, as they are read, so the relation
     * holds how each was read ({@link Derivation.AComparisonRead#counts}) — or null where what is
     * read is no comparison that keeps them, and a count is not read there.
     */
    private Map<Quantity.HowManyMeet, Derivation.AComparisonRead.Counted> counting;

    private Pullback(InputReading read, Optional<ModelOccurrence> where) {
        this.read = read;
        this.where = where;
        this.subjects = new DecisionSubjects(read.domain(), read.rules().symbols(),
                read.rules().declarations(), read.rules().newtypes());
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
     * What a comparison states, and what the arithmetic over the input made of it on the way.
     *
     * @param arithmetic read where a rule asked for it and not again, so a reader that needs to know
     *                   where that arithmetic stopped asks this rather than reading the comparison a
     *                   second time
     */
    record OnTheInput(Pulled stated, Supplier<AffineReading.OfAComparison> arithmetic) {}

    /** The same, with the arithmetic it was read through. */
    static OnTheInput ofAComparisonOnTheInput(StatedComparison comparison, InputReads reads,
                                              InputReading read) {
        Pullback reading = new Pullback(read, Optional.empty());
        Once<AffineReading.OfAComparison> arithmetic = reading.arithmeticOf(comparison, reads);
        return new OnTheInput(reading.pulled(reading.firstThatReadsIt(
                reading.rulesFor(comparison, null, false, reads, arithmetic))), arithmetic);
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
        return mayBeCarriedPast(comparison)
                && carriesPast(ofAComparison(comparison, reads, read, Optional.empty()));
    }

    /** The same, of what an emptiness check was read to state. */
    static boolean carriesPast(Pulled read) {
        // Unread anywhere in what is stated, and not among the parts it turns on: a part nothing
        // read that is the same on every run turns on nothing, and is still not read.
        Proposition stated = read.proposition();
        return !(stated instanceof Proposition.Compared)
                && !Proposition.leavesSomethingUnread(stated);
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
            if (!(concluded instanceof Proposition.Always)) {
                leaves.add(new Leaf(concluded, each.from()));
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
                    DecisionSubject subject = truthAt(e, reads);
                    return subject == null ? null
                            : leaf(new Derivation.ATruthOfASubject(subject, true), e, reads);
                },
                () -> BooleanMeaning.asAComparison(e).map(stated -> comparison(stated,
                        new Denotation(e, reads), fixed(e, reads), reads)).orElse(null),
                () -> byALaw(applied, e, AnswerAspect.TRUTH, reads, new Denotation(e, reads))));
        return taken != null ? taken
                : unread(e, reads, unreadAs(applied, AnswerAspect.TRUTH, reads));
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
        return rulesFor(stated, at, fixed, reads, arithmeticOf(stated, reads));
    }

    /** The arithmetic over the input {@code stated} is read through, when a rule asks for it. */
    private Once<AffineReading.OfAComparison> arithmeticOf(StatedComparison stated,
                                                          InputReads reads) {
        return new Once<>(() -> AffineReading.read(stated, read.domain(), reads, read.rules()));
    }

    /** The same, read through {@code arithmetic}. */
    private List<Supplier<Derivation>> rulesFor(StatedComparison stated, Denotation at,
                                                boolean fixed, InputReads reads,
                                                Once<AffineReading.OfAComparison> arithmetic) {
        AnEmptinessCheck.Checked checked = AnEmptinessCheck.checked(stated);
        return List.of(
                () -> checked == null ? null : new Derivation.AnEmptinessCheck(at == null
                        ? observe(checked.container(), AnswerAspect.EMPTINESS, reads)
                        : asking(at, () -> observe(checked.container(), AnswerAspect.EMPTINESS,
                                reads)), checked.emptyWhereItHolds()),
                () -> partOf(at, truthCompared(stated, reads)),
                () -> heldAgainstAWrittenTruth(stated, reads),
                () -> partOf(at, asACut(stated, arithmetic.get(), fixed)),
                () -> partOf(at, onAnOrder(stated, arithmetic.get(), reads)),
                () -> partOf(at, ofItsArguments(stated, fixed, reads)),
                () -> ofAChoice(stated, at, reads),
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
                () -> byALaw(applied, e, AnswerAspect.EMPTINESS, reads, asked),
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
                unreadAs(applied, AnswerAspect.EMPTINESS, reads), fixed(e, reads)), asked);
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
                () -> byALaw(applied, e, AnswerAspect.PRESENCE, reads, new Denotation(e, reads)),
                () -> {
                    DecisionSubject subject = reads.pathOf(e, read.rules().newtypes())
                            instanceof PathResolution.At(TermPath at)
                            ? new DecisionSubject.AnInput(at) : answerAt(e, reads);
                    return subject == null ? null
                            : leaf(new Derivation.PresentInASubject(subject), e, reads);
                }));
        return taken != null ? taken
                : unread(e, reads, unreadAs(applied, AnswerAspect.PRESENCE, reads));
    }

    /**
     * How many readings of one condition are made
     * ({@link CompositionBudget#READINGS_OF_ONE_CONDITION}), read here and nowhere else.
     */
    private static final CompositionBudget READINGS = CompositionBudget.READINGS_OF_ONE_CONDITION;

    /**
     * {@code block}'s body read on each of its applications in {@code at}, held to how many readings
     * of one condition are made — for every reader of a closure over values written out.
     */
    static InputReads.Applications applicationsOf(Core.Block block, InputReads at,
                                                  Symbols symbols, DeclarationNewtypes newtypes) {
        return at.applicationsOf(block, symbols, newtypes, READINGS.maximum());
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
     * InputReads#whetherEveryRowTakes}); one a row controls is a case the row writes at its position
     * or stands the dependency in with.
     */
    private Derivation ofAMatch(Core.Match match, AnswerAspect aspect, InputReads reads) {
        return armsOf(match, reads, (body, inside) -> observe(body, aspect, inside));
    }

    /**
     * Some arm of {@code match} taken, and what {@code states} reads of that arm's body where it is
     * taken — for a match a condition is, and for one that chooses a value a condition compares.
     */
    private Derivation.MatchArms armsOf(Core.Match match, InputReads reads,
                                        BiFunction<Core, InputReads, Derivation> states) {
        List<Derivation> selections = selectionsOf(match, reads);
        List<Derivation.MatchArms.Arm> arms = new ArrayList<>();
        for (int i = 0; i < match.cases().size(); i++) {
            Core.Case arm = match.cases().get(i);
            InputReads inside = reads.choosing(Choice.Decides.ofCase(match, arm),
                    read.rules().symbols(), read.rules().newtypes());
            arms.add(new Derivation.MatchArms.Arm(selections.get(i),
                    states.apply(arm.body(), inside)));
        }
        return new Derivation.MatchArms(arms);
    }

    /**
     * Whether each arm of {@code match} selects the value it matches, in the order the arms are
     * written — each on its own, and not yet that no arm before it does.
     */
    private List<Derivation> selectionsOf(Core.Match match, InputReads reads) {
        Set<TypeSymbol> written = reads.casesWritten(match.scrutinee(),
                read.rules().symbols(), read.rules().newtypes());
        DecisionSubject subject = subjectOf(new Denotation(match.scrutinee(), reads));
        // Which case the scrutinee is, read once for the match where no arm settles it on its own
        // and it is no value a row controls: every arm selects off the same reading of it.
        CasesOfAnAnswer.Answered scrutinee = null;
        List<Derivation> out = new ArrayList<>();
        for (Core.Case arm : match.cases()) {
            Optional<Boolean> every = InputReads.whetherEveryRowTakes(arm, written);
            if (every.isPresent()) {
                out.add(new Derivation.CasesWrittenOut(every.get()));
            } else if (arm.pattern() == null) {
                out.add(new Derivation.CasesWrittenOut(true));
            } else if (subject != null) {
                out.add(new Derivation.CasesOfASubject(subject,
                        CasesLeft.selectedBy(arm.pattern())));
            } else {
                if (scrutinee == null) {
                    scrutinee = answered(new Denotation(match.scrutinee(), reads),
                            WhyUnread.AtNoPosition.Place.SCRUTINEE);
                }
                out.add(selecting(scrutinee, arm));
            }
        }
        return out;
    }

    /** What a row controls that {@code value} is, where it is one: a position of the input, or what
     *  a dependency the row stands in answered. */
    private DecisionSubject subjectOf(Denotation value) {
        return value.at().pathOf(value.value(), read.rules().newtypes())
                instanceof PathResolution.At(TermPath at)
                ? new DecisionSubject.AnInput(at) : answerAt(value.value(), value.at());
    }

    /** Whether a value that is {@code answered}, read once wherever it stands, is of a case
     *  {@code arm} selects. */
    private static Derivation selecting(CasesOfAnAnswer.Answered answered, Core.Case arm) {
        return switch (answered) {
            // One of several values the source wrote out, each of which may take another arm.
            case CasesOfAnAnswer.Answered.Written(var cases) ->
                    InputReads.whetherEveryRowTakes(arm, cases)
                            .<Derivation>map(Derivation.CasesWrittenOut::new)
                            .orElseGet(() -> new Derivation.Stopped(new WhyUnread.AtNoPosition(
                                    WhyUnread.AtNoPosition.Place.SCRUTINEE), false));
            case CasesOfAnAnswer.Answered.AtAnInput(TermPath at) -> new Derivation.CasesOfASubject(
                    new DecisionSubject.AnInput(at), CasesLeft.selectedBy(arm.pattern()));
            case CasesOfAnAnswer.Answered.AtAnAnswer(var answer) -> new Derivation.CasesOfASubject(
                    answer, CasesLeft.selectedBy(arm.pattern()));
            case CasesOfAnAnswer.Answered.Unread(WhyUnread why) -> new Derivation.Stopped(why, false);
            case CasesOfAnAnswer.Answered.ByItsArms(var arms) ->
                    new Derivation.OneOfItsArms(arms.stream().map(each ->
                            new Derivation.MatchArms.Arm(each.reached(),
                                    selecting(each.answers(), arm))).toList());
        };
    }

    /**
     * Which case a behavior's body answers, over its own parameters ({@link CasesOfAnAnswer}), read
     * off {@code body} once for every call of it.
     *
     * @param parameters the names the body reads its parameters by, in the order a call hands them
     */
    static CasesOfAnAnswer answerOf(Core body, List<String> parameters, InputReads reads,
                                    InputReading read) {
        Pullback reading = new Pullback(read, Optional.empty());
        return new CasesOfAnAnswer(parameters, overItsOwnParameters(reading.answered(
                new Denotation(body, reads), WhyUnread.AtNoPosition.Place.SUBJECT)));
    }

    /**
     * {@code answered} as a body's answer read for every call of it: what a dependency answered is
     * read where a call stands, and the body read once has no such place, so that part is unread.
     */
    private static CasesOfAnAnswer.Answered overItsOwnParameters(
            CasesOfAnAnswer.Answered answered) {
        return switch (answered) {
            case CasesOfAnAnswer.Answered.AtAnAnswer _ -> new CasesOfAnAnswer.Answered.Unread(
                    new WhyUnread.InACalledBody(
                            WhyUnread.InACalledBody.What.WHAT_ITS_DEPENDENCY_ANSWERS));
            case CasesOfAnAnswer.Answered.Written _, CasesOfAnAnswer.Answered.AtAnInput _,
                 CasesOfAnAnswer.Answered.Unread _ -> answered;
            case CasesOfAnAnswer.Answered.ByItsArms(var arms) ->
                    new CasesOfAnAnswer.Answered.ByItsArms(arms.stream().map(arm ->
                            new CasesOfAnAnswer.Answered.Arm(arm.reached(),
                                    overItsOwnParameters(arm.answers()))).toList());
        };
    }

    /**
     * Which case {@code value} is, where it stands: written in arms where it is chosen by them, and
     * at each arm what that arm answers.
     *
     * <p>The one reading of it, for a body's answer and for the value a {@code match} chooses its
     * arm by alike.
     *
     * @param nowhere what the value is, as the place it stands at no position, where it is made of
     *                nothing followed back to the input
     */
    private CasesOfAnAnswer.Answered answered(Denotation value,
                                              WhyUnread.AtNoPosition.Place nowhere) {
        Denotation chosen = chosenAt(value);
        if (chosen != null) {
            long most = READINGS.maximum();
            if (value.at().readings() * readingsOf(value, most) > most) {
                return new CasesOfAnAnswer.Answered.Unread(new WhyUnread.MoreReadingsThanAreMade());
            }
            return answeredByItsArms(chosen, nowhere);
        }
        Set<TypeSymbol> written = value.at().casesWritten(value.value(), read.rules().symbols(),
                read.rules().newtypes());
        if (written != null && !written.isEmpty()) {
            return new CasesOfAnAnswer.Answered.Written(written);
        }
        if (value.at().pathOf(value.value(), read.rules().newtypes())
                instanceof PathResolution.At(TermPath at)) {
            return new CasesOfAnAnswer.Answered.AtAnInput(at);
        }
        DecisionSubject.AnAnswer answer = answerAt(value.value(), value.at());
        if (answer != null) {
            return new CasesOfAnAnswer.Answered.AtAnAnswer(answer);
        }
        CasesOfAnAnswer.Answered called = calledFor(value);
        // Made of nothing followed back to the input: what an operation answers, or a value the
        // source works out.
        return called != null ? called : new CasesOfAnAnswer.Answered.Unread(
                new WhyUnread.AtNoPosition(nowhere));
    }

    /** {@code chosen}'s arms, each reached where a run takes it and answering what it does. */
    private CasesOfAnAnswer.Answered answeredByItsArms(Denotation chosen,
                                                       WhyUnread.AtNoPosition.Place nowhere) {
        InputReads where = chosen.at();
        List<CasesOfAnAnswer.Answered.Arm> arms = new ArrayList<>();
        switch (Core.withoutStanding(chosen.value())) {
            case Core.If iff -> {
                Derivation cond = observe(iff.cond(), AnswerAspect.TRUTH, where);
                arms.add(new CasesOfAnAnswer.Answered.Arm(cond,
                        answered(new Denotation(iff.then(), where), nowhere)));
                arms.add(new CasesOfAnAnswer.Answered.Arm(new Derivation.UnderADenial(cond, true),
                        answered(new Denotation(iff.els(), where), nowhere)));
            }
            case Core.Match match -> {
                List<Derivation> selections = selectionsOf(match, where);
                for (int i = 0; i < match.cases().size(); i++) {
                    Core.Case arm = match.cases().get(i);
                    InputReads inside = where.choosing(Choice.Decides.ofCase(match, arm),
                            read.rules().symbols(), read.rules().newtypes());
                    arms.add(new CasesOfAnAnswer.Answered.Arm(
                            new Derivation.AnArmTaken(selections.subList(0, i), selections.get(i)),
                            answered(new Denotation(arm.body(), inside), nowhere)));
                }
            }
            case Core.IfConstructed attempt -> {
                List<Derivation> taken = attempted(attempt, where);
                List<Choice.Arm> choice = Choice.of(attempt).arms();
                for (int i = 0; i < choice.size(); i++) {
                    InputReads inside = where.choosing(choice.get(i).decidedBy(),
                            read.rules().symbols(), read.rules().newtypes());
                    arms.add(new CasesOfAnAnswer.Answered.Arm(taken.get(i),
                            answered(new Denotation(choice.get(i).answers(), inside), nowhere)));
                }
            }
            // A value one of whose arguments an operation of the library answers by how they
            // stand, which is a number and of no case.
            default -> {
                return new CasesOfAnAnswer.Answered.Unread(new WhyUnread.NotYetComposed(
                        WhyUnread.NotYetComposed.Step.A_CHOICE_BY_CASES));
            }
        }
        return new CasesOfAnAnswer.Answered.ByItsArms(arms);
    }

    /**
     * What {@code value} answers where it is a call of a behavior that is no dependency the row
     * stands in — read once off that behavior's body and put in at this call — or null where it is
     * no such call.
     */
    private CasesOfAnAnswer.Answered calledFor(Denotation value) {
        Denotation stands = value.at().standing(value.value(), read.rules().symbols(),
                read.rules().newtypes());
        if (!(AnOperationApplied.of(Core.withoutStanding(stands.value()))
                instanceof AnOperationApplied(ValueName.Behavior behavior, List<Core> args))
                || stands.at().standsIn(behavior)) {
            return null;
        }
        Optional<CasesOfAnAnswer> found = read.rules().declarations().answers().of(behavior);
        if (found.isEmpty()) {
            return new CasesOfAnAnswer.Answered.Unread(new WhyUnread.InACalledBody(
                    WhyUnread.InACalledBody.What.AN_ANSWER_NOT_READ));
        }
        CasesOfAnAnswer cases = found.get();
        if (cases.answered() instanceof CasesOfAnAnswer.Answered.Unread unread) {
            return unread;
        }
        if (args.size() != cases.parameters().size()) {
            return new CasesOfAnAnswer.Answered.Unread(new WhyUnread.InACalledBody(
                    WhyUnread.InACalledBody.What.AN_ANSWER_NOT_READ));
        }
        Map<String, TermPath> handed = new HashMap<>();
        Map<String, Set<TypeSymbol>> written = new HashMap<>();
        for (int i = 0; i < args.size(); i++) {
            String parameter = cases.parameters().get(i);
            if (stands.at().pathOf(args.get(i), read.rules().newtypes())
                    instanceof PathResolution.At(TermPath at)) {
                handed.put(parameter, at);
            } else {
                Set<TypeSymbol> one = stands.at().casesWritten(args.get(i),
                        read.rules().symbols(), read.rules().newtypes());
                if (one != null && !one.isEmpty()) {
                    written.put(parameter, one);
                }
            }
        }
        return atTheCall(cases.answered(), behavior, handed, written);
    }

    /**
     * {@code answered}, read off a body over its parameters, at a call that handed each parameter
     * named in {@code handed} the position there and each named in {@code written} a value written
     * out: where the body's answer stands is moved to the same way into what the call handed, and
     * where an arm is reached is said of what the call handed ({@link
     * Derivation.ABehaviorsAnswerAtACall}).
     */
    private static CasesOfAnAnswer.Answered atTheCall(CasesOfAnAnswer.Answered answered,
                                                      ValueName.Behavior behavior,
                                                      Map<String, TermPath> handed,
                                                      Map<String, Set<TypeSymbol>> written) {
        return switch (answered) {
            case CasesOfAnAnswer.Answered.Written _, CasesOfAnAnswer.Answered.Unread _ -> answered;
            // A body's answer read for every call holds none ({@link CasesOfAnAnswer}).
            case CasesOfAnAnswer.Answered.AtAnAnswer _ -> throw new IllegalArgumentException(
                    "a body's answer over its own parameters names no dependency's answer: "
                            + answered);
            case CasesOfAnAnswer.Answered.AtAnInput(TermPath at) when handed.containsKey(at.head()) ->
                    new CasesOfAnAnswer.Answered.AtAnInput(at.under(handed.get(at.head())));
            case CasesOfAnAnswer.Answered.AtAnInput(TermPath at)
                    when at.steps().isEmpty() && written.containsKey(at.head()) ->
                    new CasesOfAnAnswer.Answered.Written(written.get(at.head()));
            case CasesOfAnAnswer.Answered.AtAnInput _ -> new CasesOfAnAnswer.Answered.Unread(
                    new WhyUnread.InACalledBody(
                            WhyUnread.InACalledBody.What.AN_ARGUMENT_AT_NO_POSITION));
            case CasesOfAnAnswer.Answered.ByItsArms(var arms) ->
                    new CasesOfAnAnswer.Answered.ByItsArms(arms.stream().map(arm ->
                            new CasesOfAnAnswer.Answered.Arm(
                                    new Derivation.ABehaviorsAnswerAtACall(behavior,
                                            arm.reached(), handed),
                                    atTheCall(arm.answers(), behavior, handed, written)))
                            .toList());
        };
    }

    /**
     * What a run entering each arm of {@code fork} — a {@code match}, or an attempted construction
     * — states, where {@code fork} is read in {@code reads}.
     *
     * <p>Every arm at once, because what one arm states is a fact of the whole fork: the arms
     * before it not taken and its own taken. So the fork is read once — a {@code match}'s
     * selections, an attempt's clauses — and each arm concluded off that one reading.
     *
     * <p>The arms as {@link Choice} numbers them: a {@code match}'s in the order they are written,
     * and an attempt's built arm first and then its departures as written.
     *
     * @param where the construct of the model the fork is, where the caller knows it
     */
    static List<Pulled> ofTheArms(Core fork, InputReads reads, InputReading read,
                                  Optional<ModelOccurrence> where) {
        Pullback reading = new Pullback(read, where);
        return reading.entering(fork, reads).stream().map(reading::pulled).toList();
    }

    private List<Derivation> entering(Core fork, InputReads reads) {
        return switch (Core.withoutStanding(fork)) {
            case Core.Match match -> {
                List<Derivation> selections = selectionsOf(match, reads);
                List<Derivation> out = new ArrayList<>();
                for (int part = 0; part < selections.size(); part++) {
                    out.add(new Derivation.AnArmTaken(selections.subList(0, part),
                            selections.get(part)));
                }
                yield out;
            }
            case Core.IfConstructed attempt -> attempted(attempt, reads);
            default -> throw new IllegalArgumentException(fork.getClass().getSimpleName()
                    + " at " + fork.pos() + " is no match or attempt with arms a run enters");
        };
    }

    /**
     * What each arm of {@code attempt} being taken states, in the order {@link Choice} numbers
     * them: the value built, where every clause of the invariant holds of what the attempt hands
     * it; and each departure, where the first clause not to hold is one it answers.
     *
     * <p>A departure naming a clause answers that clause, and one naming none answers every clause
     * no other departure names. A clause this reading could not read stands in its place, since
     * whether it holds decides the arms after it as much as one that was read.
     */
    private List<Derivation> attempted(Core.IfConstructed attempt, InputReads reads) {
        ClausesInOrder clauses = ClausesInOrder.at(attempt.construct(), read.rules());
        if (!clauses.everyRuleReached()) {
            return Collections.nCopies(1 + attempt.els().size(), new Derivation.Stopped(
                    new WhyUnread.AnInvariantNotReached(), false));
        }
        List<Derivation> holds = new ArrayList<>();
        for (ClausesInOrder.OneClause clause : clauses.inOrder()) {
            holds.add(switch (clause) {
                case ClausesInOrder.OneClause.Stated stated ->
                        observe(stated.states(), AnswerAspect.TRUTH, reads);
                case ClausesInOrder.OneClause.Unread unread -> new Derivation.Stopped(
                        new WhyUnread.AClauseOfAnInvariant(unread.clause(), unread.why()), false);
            });
        }
        Set<ClauseName> named = new HashSet<>();
        attempt.els().forEach(arm -> arm.clause().ifPresent(name ->
                named.add(new ClauseName(name))));
        List<Derivation> out = new ArrayList<>();
        out.add(new Derivation.ItWasBuilt(holds));
        for (Core.ElseArm arm : attempt.els()) {
            Optional<ClauseName> answering = arm.clause().map(ClauseName::new);
            List<Boolean> answers = clauses.inOrder().stream()
                    .map(clause -> answering.isPresent()
                            ? clause.clause().name().equals(answering)
                            : clause.clause().name().map(name -> !named.contains(name))
                                    .orElse(true))
                    .toList();
            out.add(new Derivation.ItDeparted(holds, answers));
        }
        return out;
    }

    /**
     * How {@code applied} coming out on {@code aspect} was read by what settles that side of its
     * answer: its law, read over the arguments it was handed, or the closing that names what the
     * domain has no words for, stopped at {@code stopsAt} — or null where nothing settles it.
     */
    private Derivation byALaw(AnOperationApplied applied, Core e, AnswerAspect aspect,
                              InputReads reads, Denotation stopsAt) {
        if (applied == null || !(applied.operation() instanceof ValueName.Stdlib operation)) {
            return null;
        }
        return switch (DefaultBoundOperationFacts.get().settled(operation,
                OperationLaw.Observed.of(aspect))) {
            case null -> null;
            case BoundOperationFacts.Settled.Unsaid(Unsayable why) -> leaf(new Derivation.Stopped(
                    new WhyUnread.NoWordsFor(operation, aspect, why), fixed(e, reads)), stopsAt);
            case BoundOperationFacts.Settled.ByALaw(
                    OperationLaw.Observation<DeclaredArgument> law, var _) ->
                    new Derivation.ByALaw(operation, aspect,
                            new ALawRead(applied, e, reads).of(law.equivalentTo()));
            case BoundOperationFacts.Settled.ByALaw(OperationLaw.Size<DeclaredArgument> _, var _) ->
                    throw new IllegalStateException(operation + " settles a side of its answer"
                            + " with how many it holds");
        };
    }

    /**
     * How many {@code value}, read in {@code at}, holds, as a number of the quantities a condition
     * is read over: the size of a position, or the size an operation's law says its answer has.
     */
    private sealed interface Sized {

        record AsAForm(LinearForm<Quantity> form) implements Sized {}

        record NotSized(WhyUnread why) implements Sized {}
    }

    /** What an element a law names is, inside a statement about some element of its container. */
    private sealed interface ElementAt {

        /** The element of the container at {@code container}, which a row writes. */
        record AtAPosition(TermPath container) implements ElementAt {}

        /** A value the source wrote out, read in {@code at}. */
        record WrittenOut(Core value, InputReads at) implements ElementAt {}
    }

    /** A statement read of each value a container written out holds, or why it was not. */
    private sealed interface WrittenOutRead {

        record Each(List<Derivation> each) implements WrittenOutRead {}

        record Stops(WhyUnread why) implements WrittenOutRead {}
    }

    private Sized sizeOf(Core value, InputReads at) {
        if (at.pathOf(value, read.rules().newtypes()) instanceof PathResolution.At(TermPath held)) {
            NumericTerm.TakenOf size = sizeAt(held);
            return size == null ? new Sized.NotSized(new WhyUnread.NoMeasureOfItsSize())
                    : new Sized.AsAForm(LinearForm.atom(new DecisionAtom.OfTheInput(size)));
        }
        Denotation made = at.standing(value, read.rules().symbols(), read.rules().newtypes());
        if (!(AnOperationApplied.of(Core.withoutStanding(made.value()))
                instanceof AnOperationApplied applied
                && applied.operation() instanceof ValueName.Stdlib operation)) {
            return new Sized.NotSized(
                    new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT));
        }
        if (!(DefaultBoundOperationFacts.get().settled(operation, OperationLaw.Observed.SIZE)
                instanceof BoundOperationFacts.Settled.ByALaw(
                        OperationLaw.Size<DeclaredArgument> law, var _))) {
            ValueName.Stdlib measure = NumericMeasures.takenOf(value.type(), read.rules().inners());
            return new Sized.NotSized(measure == null
                    ? new WhyUnread.NoMeasureOfItsSize()
                    : new WhyUnread.ANumberOfWhatAnOperationAnswers(measure, operation));
        }
        return new ALawRead(applied, Core.withoutStanding(made.value()), made.at())
                .number(law.equalTo());
    }

    /** The number a size of the container at {@code held} is, or null where no type measures it. */
    private NumericTerm.TakenOf sizeAt(TermPath held) {
        Type container = read.domain().typeAt(held, read.rules());
        ValueName.Stdlib size = container == null ? null
                : NumericMeasures.takenOf(container, read.rules().inners());
        return size == null ? null : NumericTerm.TakenOf.of(size, held, container,
                read.rules().inners(), read.rules().symbols());
    }

    /**
     * A law of {@code applied}, read over the arguments it was handed where it stands at {@code e}
     * in {@code reads}.
     *
     * <p>Each word of the law is read by the rule the reading of a condition already has for it:
     * an argument observed is that argument observed, a number of the arguments is what the
     * arithmetic reads, some element is the quantifier over the container's element. So a law says
     * only what the operation does, and every part of what it comes to is read where it stands.
     */
    private final class ALawRead {

        private final AnOperationApplied applied;
        private final Core e;
        private final InputReads reads;
        /** The containers a statement about some element of each is being read inside, and what
         *  the element is there. */
        private final Map<DeclaredArgument, ElementAt> elements = new HashMap<>();
        /** Where the closure's body is read, where one application of it is: a container written
         *  out hands it one value at a time. */
        private InputReads application;

        ALawRead(AnOperationApplied applied, Core e, InputReads reads) {
            this.applied = applied;
            this.e = e;
            this.reads = reads;
        }

        Derivation of(LawProposition<DeclaredArgument> law) {
            return switch (law) {
                case LawProposition.Always<DeclaredArgument>(boolean holds) ->
                        new Derivation.ALawSettles(holds);
                case LawProposition.All<DeclaredArgument> all ->
                        new Derivation.ALawJoins(all.parts().stream().map(this::of).toList(), true);
                case LawProposition.Any<DeclaredArgument> any ->
                        new Derivation.ALawJoins(any.parts().stream().map(this::of).toList(),
                                false);
                case LawProposition.Observed<DeclaredArgument> observed ->
                        new Derivation.OnTheSideALawNames(
                                observed(observed.of(), observed.side().aspect()),
                                observed.side().holds());
                case LawProposition.Compared<DeclaredArgument> compared ->
                        compared(compared.form(), compared.states());
                case LawProposition.SomeElement<DeclaredArgument> some -> some(some);
                case LawProposition.Same<DeclaredArgument> same -> {
                    DecisionSubject one = subject(same.one());
                    DecisionSubject other = subject(same.other());
                    yield one == null || other == null
                            ? unread(e, reads,
                                    new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.VALUE))
                            : leaf(new Derivation.TheSameValue(one, other, same.holds()), e, reads);
                }
            };
        }

        /** How {@code subject} coming out on {@code aspect}'s holding side was read. */
        private Derivation observed(LawSubject<DeclaredArgument> subject, AnswerAspect aspect) {
            return switch (subject) {
                case LawSubject.Argument<DeclaredArgument>(DeclaredArgument at) ->
                        observe(applied.argument(at), aspect, reads);
                case LawSubject.ElementOf<DeclaredArgument>(DeclaredArgument at) ->
                        switch (elements.get(at)) {
                            // A value written out is read as itself, where it was written.
                            case ElementAt.WrittenOut(Core value, InputReads in) ->
                                    observe(value, aspect, in);
                            case ElementAt.AtAPosition(TermPath container) -> {
                                TermPath element = container.element();
                                yield switch (aspect) {
                                    case TRUTH -> leaf(new Derivation.ATruthOfASubject(
                                            new DecisionSubject.AnInput(element), true), e, reads);
                                    case PRESENCE -> leaf(new Derivation.PresentInASubject(
                                            new DecisionSubject.AnInput(element)), e, reads);
                                    case EMPTINESS -> {
                                        Derivation some = holdsSomethingAt(element);
                                        yield leaf(some != null ? some : new Derivation.Stopped(
                                                new WhyUnread.NoMeasureOfItsSize(), false), e,
                                                reads);
                                    }
                                };
                            }
                        };
                case LawSubject.WhatTheClosureAnswers<DeclaredArgument>(DeclaredArgument at) -> {
                    Denotation closure = reads.denotes(applied.argument(at),
                            read.rules().symbols(), read.rules().newtypes());
                    yield Core.withoutStanding(closure.value()) instanceof Core.Block block
                            ? observe(block.body(), aspect,
                                    application != null ? application : closure.at())
                            : unread(e, reads, new WhyUnread.NotYetComposed(
                                    WhyUnread.NotYetComposed.Step.A_CLOSURE_BY_NAME));
                }
            };
        }

        /** The subject a row controls {@code subject} is, or null where it is none. */
        private DecisionSubject subject(LawSubject<DeclaredArgument> subject) {
            return switch (subject) {
                case LawSubject.Argument<DeclaredArgument>(DeclaredArgument at) -> {
                    Core value = applied.argument(at);
                    yield reads.pathOf(value, read.rules().newtypes())
                            instanceof PathResolution.At(TermPath held)
                            ? new DecisionSubject.AnInput(held) : answerAt(value, reads);
                }
                case LawSubject.ElementOf<DeclaredArgument>(DeclaredArgument at) ->
                        switch (elements.get(at)) {
                            case ElementAt.AtAPosition(TermPath container) ->
                                    new DecisionSubject.AnInput(container.element());
                            case ElementAt.WrittenOut(Core value, InputReads in) ->
                                    in.pathOf(value, read.rules().newtypes())
                                            instanceof PathResolution.At(TermPath held)
                                            ? new DecisionSubject.AnInput(held)
                                            : answerAt(value, in);
                        };
                case LawSubject.WhatTheClosureAnswers<DeclaredArgument> _ -> null;
            };
        }

        /**
         * Some element of a container meeting a statement, read as the quantifier over the
         * container's element where it stands, or element by element where it was written out.
         */
        private Derivation some(LawProposition.SomeElement<DeclaredArgument> some) {
            Core over = applied.argument(some.container());
            Derivation meeting = meeting(over, some);
            return some.holds() ? meeting : new Derivation.OnTheSideALawNames(meeting, false);
        }

        private Derivation meeting(Core over, LawProposition.SomeElement<DeclaredArgument> some) {
            Denotation container = reads.standing(over, read.rules().symbols(),
                    read.rules().newtypes());
            // A container the source wrote out has some element meeting a statement where one of
            // the values it writes out does.
            if (Core.withoutStanding(container.value()) instanceof Core.ListLit list) {
                return switch (ofEachWrittenOut(some.container(), list, container.at(),
                        some.ofTheElement())) {
                    case WrittenOutRead.Each(List<Derivation> each) ->
                            new Derivation.OverElementsWrittenOut(each, true);
                    case WrittenOutRead.Stops(WhyUnread why) -> unread(e, reads, why);
                };
            }
            if (!(reads.pathOf(over, read.rules().newtypes()) instanceof PathResolution.At(
                    TermPath held))) {
                return unread(over, reads,
                        new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.CONTAINER));
            }
            Derivation answered = aboutAnElement(some.container(), held, some.ofTheElement());
            if (answered == null) {
                return unread(e, reads, new WhyUnread.TwoElementsOfOneContainer());
            }
            Proposition element = trying.of(answered);
            Optional<Derivation> holdsSomething = Optional.empty();
            if (Derivation.SomeElementMeeting.asksWhetherItHoldsAnything(held, element)) {
                NumericTerm.TakenOf size = sizeAt(held);
                holdsSomething = Optional.of(size != null
                        ? leaf(new Derivation.SizeAboveNought(size),
                                askedAt != null ? askedAt : new Denotation(e, reads))
                        : unread(over, reads, new WhyUnread.NoMeasureOfItsSize()));
            }
            return new Derivation.SomeElementMeeting(held, answered, true, holdsSomething);
        }

        /**
         * {@code ofTheElement} read of the element of {@code container}, which stands at
         * {@code held} — or null where that container is already quantified over: the element is
         * what stands at the container's element, so the same container quantified inside itself
         * would name two elements one subject.
         */
        private Derivation aboutAnElement(DeclaredArgument container, TermPath held,
                                          LawProposition<DeclaredArgument> ofTheElement) {
            if (!quantifying.add(held)) {
                return null;
            }
            elements.put(container, new ElementAt.AtAPosition(held));
            try {
                return of(ofTheElement);
            } finally {
                elements.remove(container);
                quantifying.remove(held);
            }
        }

        /**
         * {@code law} read of each value {@code list}, written out at {@code at} as the container
         * {@code container}, holds: of the value itself where the law names the element, and of
         * what the closure states on the application that hands it that value where the law names
         * what the closure answers.
         *
         * <p>Where which value one application hands cannot be said, the closure's body is read
         * once with its parameter standing for all of them ({@code ReadMeaning.OneOf}), which
         * states of the input only what they agree on. A law naming both the element and the
         * closure would have to pair each value with its application, which nothing here does.
         */
        private WrittenOutRead ofEachWrittenOut(DeclaredArgument container, Core.ListLit list,
                                                InputReads at,
                                                LawProposition<DeclaredArgument> law) {
            if (list.elements().isEmpty()) {
                return new WrittenOutRead.Each(List.of());
            }
            DeclaredArgument named = closureIn(law);
            boolean element = namesTheElement(law, container);
            if (named != null && element) {
                return new WrittenOutRead.Stops(new WhyUnread.NotYetComposed(
                        WhyUnread.NotYetComposed.Step.VALUES_WRITTEN_OUT));
            }
            List<Derivation> ofEach = new ArrayList<>();
            if (named == null) {
                if (list.elements().size() > READINGS.maximum()) {
                    return new WrittenOutRead.Stops(new WhyUnread.MoreReadingsThanAreMade());
                }
                for (Core value : list.elements()) {
                    elements.put(container, new ElementAt.WrittenOut(value, at));
                    try {
                        ofEach.add(of(law));
                    } finally {
                        elements.remove(container);
                    }
                }
                return new WrittenOutRead.Each(ofEach);
            }
            Denotation closure = reads.denotes(applied.argument(named), read.rules().symbols(),
                    read.rules().newtypes());
            if (!(Core.withoutStanding(closure.value()) instanceof Core.Block block)) {
                return new WrittenOutRead.Stops(new WhyUnread.NotYetComposed(
                        WhyUnread.NotYetComposed.Step.A_CLOSURE_BY_NAME));
            }
            List<InputReads> applications = switch (applicationsOf(block, closure.at(),
                    read.rules().symbols(), read.rules().newtypes())) {
                case InputReads.Applications.Each(var each, var _) -> each;
                case InputReads.Applications.NoneHanded _, InputReads.Applications.Unsaid _ ->
                        List.of(closure.at());
                case InputReads.Applications.MoreThanAreRead _ -> null;
            };
            if (applications == null) {
                return new WrittenOutRead.Stops(new WhyUnread.MoreReadingsThanAreMade());
            }
            InputReads outer = application;
            try {
                for (InputReads one : applications) {
                    application = one;
                    ofEach.add(of(law));
                }
            } finally {
                application = outer;
            }
            return new WrittenOutRead.Each(ofEach);
        }


        /**
         * {@code form states 0}, over numbers of the arguments, read as a relation over the
         * quantities a condition is read over.
         */
        private Derivation compared(LinearForm<LawNumber<DeclaredArgument>> form, Rel states) {
            Map<Quantity.HowManyMeet, Derivation.AComparisonRead.Counted> outer = counting;
            counting = new LinkedHashMap<>();
            try {
                List<LinearForm<Quantity>> parts = new ArrayList<>();
                Sized sized = number(form, parts);
                return switch (sized) {
                    case Sized.NotSized(WhyUnread why) ->
                            leaf(new Derivation.Stopped(why, fixed(e, reads)), e, reads);
                    case Sized.AsAForm(LinearForm<Quantity> read) -> read.coefs().isEmpty()
                            ? new Derivation.ACutThatCutsNothing(
                                    states.holds(read.constant().signum()), ofTheInputIn(parts))
                            : leaf(aRelation(Derivation.ComparisonReading.BY_A_LAW, read, states,
                                    counting), e, reads);
                };
            } finally {
                counting = outer;
            }
        }

        /** {@code form}, a number of the arguments, as a form over the quantities a condition is
         *  read over. */
        Sized number(LinearForm<LawNumber<DeclaredArgument>> form) {
            return number(form, new ArrayList<>());
        }

        /** The same, with what each number of it was read as put in {@code parts}, before any of
         *  them cancels. */
        private Sized number(LinearForm<LawNumber<DeclaredArgument>> form,
                             List<LinearForm<Quantity>> parts) {
            List<LinearForm<Quantity>> scaled = new ArrayList<>();
            scaled.add(LinearForm.constant(form.constant()));
            for (Map.Entry<LawNumber<DeclaredArgument>, ExactRatio> term : form.coefs().entrySet()) {
                Sized part = atom(term.getKey());
                if (!(part instanceof Sized.AsAForm(LinearForm<Quantity> each))) {
                    return part;
                }
                parts.add(each);
                switch (each.times(term.getValue())) {
                    case ExactAnswer.Held<LinearForm<Quantity>> held -> scaled.add(held.value());
                    case ExactAnswer.Unheld<LinearForm<Quantity>> unheld -> {
                        return new Sized.NotSized(new WhyUnread.ANumberNotHeld(unheld.why()));
                    }
                }
            }
            // Every part's weights added at once, so whether they are held does not turn on which
            // part came first.
            return switch (LinearForm.sum(scaled)) {
                case ExactAnswer.Held<LinearForm<Quantity>> held -> new Sized.AsAForm(held.value());
                case ExactAnswer.Unheld<LinearForm<Quantity>> unheld ->
                        new Sized.NotSized(new WhyUnread.ANumberNotHeld(unheld.why()));
            };
        }

        private Sized atom(LawNumber<DeclaredArgument> number) {
            return switch (number) {
                case LawNumber.AnArgument<DeclaredArgument>(DeclaredArgument at) ->
                        switch (AffineForms.outcome(applied.argument(at), reads, quantities())) {
                            case AffineForms.Outcome.Composed<Quantity, InputReads>(var form) ->
                                    new Sized.AsAForm(form);
                            case AffineForms.Outcome.StoppedAt<Quantity, InputReads> stopped ->
                                    new Sized.NotSized(noFormOf(stopped));
                        };
                case LawNumber.SizeOf<DeclaredArgument>(LawSubject<DeclaredArgument> of) ->
                        switch (of) {
                            case LawSubject.Argument<DeclaredArgument>(DeclaredArgument at) ->
                                    sizeOf(applied.argument(at), reads);
                            case LawSubject.ElementOf<DeclaredArgument>(DeclaredArgument at) ->
                                    switch (elements.get(at)) {
                                        case ElementAt.WrittenOut(Core value, InputReads in) ->
                                                sizeOf(value, in);
                                        case ElementAt.AtAPosition(TermPath container) -> {
                                            NumericTerm.TakenOf size = sizeAt(container.element());
                                            yield size == null ? new Sized.NotSized(
                                                    new WhyUnread.NoMeasureOfItsSize())
                                                    : new Sized.AsAForm(LinearForm.atom(
                                                            new DecisionAtom.OfTheInput(size)));
                                        }
                                    };
                            case LawSubject.WhatTheClosureAnswers<DeclaredArgument> _ ->
                                    new Sized.NotSized(new WhyUnread.AtNoPosition(
                                            WhyUnread.AtNoPosition.Place.SUBJECT));
                        };
                case LawNumber.HowManyMeet<DeclaredArgument> counted -> count(counted);
            };
        }

        /** How many elements of a container meet a statement, as one count of the quantities a
         *  relation is written over. */
        private Sized count(LawNumber.HowManyMeet<DeclaredArgument> counted) {
            Core over = applied.argument(counted.container());
            Denotation container = reads.standing(over, read.rules().symbols(),
                    read.rules().newtypes());
            // Of values written out, how many meet the statement is how many of the statements
            // about each of them hold: a number where each of them settles whether it does, and
            // beside that how many of the rest hold, which is read as which of them do where it is
            // compared.
            if (Core.withoutStanding(container.value()) instanceof Core.ListLit list) {
                return switch (ofEachWrittenOut(counted.container(), list, container.at(),
                        counted.ofTheElement())) {
                    case WrittenOutRead.Stops(WhyUnread why) -> new Sized.NotSized(why);
                    case WrittenOutRead.Each(List<Derivation> each) -> {
                        long meeting = 0;
                        List<Proposition> unsettled = new ArrayList<>();
                        for (Derivation one : each) {
                            Proposition stated = trying.of(one);
                            WhyUnread stopped = Proposition.firstStopIn(stated);
                            if (stopped != null) {
                                yield new Sized.NotSized(stopped);
                            }
                            if (stated instanceof Proposition.Always(boolean holds)) {
                                meeting += holds ? 1 : 0;
                            } else {
                                unsettled.add(stated);
                            }
                        }
                        LinearForm<Quantity> settled = LinearForm.constant(ExactRatio.of(meeting));
                        if (unsettled.isEmpty()) {
                            yield new Sized.AsAForm(settled);
                        }
                        // Which of them hold is a choice for each, so the readings double with
                        // every one; past the readings one condition is read in, it is not read.
                        if (unsettled.size() >= Long.SIZE - 1
                                || (1L << unsettled.size()) > READINGS.maximum()) {
                            yield new Sized.NotSized(new WhyUnread.MoreReadingsThanAreMade());
                        }
                        yield new Sized.AsAForm(new LinearForm<>(settled.constant(),
                                Map.of(new Quantity.HowManyHold(unsettled), ExactRatio.ONE)));
                    }
                };
            }
            if (counting == null || !(reads.pathOf(over, read.rules().newtypes())
                    instanceof PathResolution.At(TermPath held))) {
                return new Sized.NotSized(
                        new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.CONTAINER));
            }
            Derivation answered = aboutAnElement(counted.container(), held,
                    counted.ofTheElement());
            if (answered == null) {
                return new Sized.NotSized(new WhyUnread.TwoElementsOfOneContainer());
            }
            Proposition element = trying.of(answered);
            WhyUnread stopped = Proposition.firstStopIn(element);
            if (stopped != null) {
                return new Sized.NotSized(stopped);
            }
            // What is the same for every element counts all of them or none.
            if (!element.mayTurnOnAnElementOf(held)) {
                if (element instanceof Proposition.Always(boolean holds)) {
                    NumericTerm.TakenOf size = sizeAt(held);
                    return !holds ? new Sized.AsAForm(LinearForm.constant(ExactRatio.ZERO))
                            : size == null ? new Sized.NotSized(new WhyUnread.NoMeasureOfItsSize())
                            : new Sized.AsAForm(LinearForm.atom(new DecisionAtom.OfTheInput(size)));
                }
                return new Sized.NotSized(new WhyUnread.OutsideTheLinearFragment());
            }
            Quantity.HowManyMeet count = new Quantity.HowManyMeet(held, element);
            counting.putIfAbsent(count, new Derivation.AComparisonRead.Counted(held, answered));
            return new Sized.AsAForm(LinearForm.atom(count));
        }
    }

    /** The closure {@code law} names what it answers of, or null where it names none. */
    private static DeclaredArgument closureIn(LawProposition<DeclaredArgument> law) {
        return switch (law) {
            case LawProposition.Always<DeclaredArgument> _,
                 LawProposition.Compared<DeclaredArgument> _,
                 LawProposition.Same<DeclaredArgument> _ -> null;
            case LawProposition.All<DeclaredArgument> all -> closureIn(all.parts());
            case LawProposition.Any<DeclaredArgument> any -> closureIn(any.parts());
            case LawProposition.Observed<DeclaredArgument> observed ->
                    observed.of() instanceof LawSubject.WhatTheClosureAnswers<DeclaredArgument>(
                            DeclaredArgument closure) ? closure : null;
            case LawProposition.SomeElement<DeclaredArgument> some ->
                    closureIn(some.ofTheElement());
        };
    }

    private static DeclaredArgument closureIn(List<LawProposition<DeclaredArgument>> parts) {
        for (LawProposition<DeclaredArgument> part : parts) {
            DeclaredArgument closure = closureIn(part);
            if (closure != null) {
                return closure;
            }
        }
        return null;
    }

    /** Whether {@code law} names an element of {@code container} anywhere in it. */
    private static boolean namesTheElement(LawProposition<DeclaredArgument> law,
                                           DeclaredArgument container) {
        return switch (law) {
            case LawProposition.Always<DeclaredArgument> _ -> false;
            case LawProposition.All<DeclaredArgument> all -> all.parts().stream()
                    .anyMatch(part -> namesTheElement(part, container));
            case LawProposition.Any<DeclaredArgument> any -> any.parts().stream()
                    .anyMatch(part -> namesTheElement(part, container));
            case LawProposition.Observed<DeclaredArgument> observed ->
                    observed.of().equals(new LawSubject.ElementOf<>(container));
            case LawProposition.Compared<DeclaredArgument> compared -> compared.form().coefs()
                    .keySet().stream().anyMatch(number -> switch (number) {
                        case LawNumber.AnArgument<DeclaredArgument> _ -> false;
                        case LawNumber.SizeOf<DeclaredArgument>(var of) ->
                                of.equals(new LawSubject.ElementOf<>(container));
                        case LawNumber.HowManyMeet<DeclaredArgument> inner ->
                                namesTheElement(inner.ofTheElement(), container);
                    });
            case LawProposition.SomeElement<DeclaredArgument> some ->
                    namesTheElement(some.ofTheElement(), container);
            case LawProposition.Same<DeclaredArgument> same ->
                    same.one().equals(new LawSubject.ElementOf<>(container))
                            || same.other().equals(new LawSubject.ElementOf<>(container));
        };
    }



    /** That the container at {@code held} holds something, as its size above nought — or null
     *  where its size is no term of this input. */
    private Derivation holdsSomethingAt(TermPath held) {
        NumericTerm.TakenOf count = sizeAt(held);
        return count == null ? null : new Derivation.SizeAboveNought(count);
    }

    /**
     * A comparison read as a relation over the quantities a condition is read over: numbers of the
     * input, numbers dependencies answered, and numbers of values the body bound — or unread where
     * some part of it is none of them.
     *
     * <p>The last rule for a comparison, and the one that takes every comparison: what reads the
     * input alone is tried before it. It reads what those cannot: a number a row stands a
     * dependency in with, and a value whose making is unknown, such as what an attempt built. Which
     * value that is is still known, by the binding that names it, and two comparisons over one name
     * are about one number. The arithmetic is {@link AffineForms}'s, the one walk every
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
        return overQuantities(new Denotation(comparison.left(), reads),
                new Denotation(comparison.right(), reads), comparison.claim().statedRelation());
    }

    /**
     * {@code left states right}, each side read where it stands, as a relation over the quantities
     * a condition is read over — or unread where a side is no form over them.
     *
     * <p>Each side in its own names, because what is related is two numbers and not two spellings:
     * an atom of these quantities is a number of the input, an answer or a binding, none of which
     * turns on the names in force where it was read, so two forms are put together wherever each
     * was read.
     */
    private Derivation overQuantities(Denotation left, Denotation right, Rel states) {
        Map<Quantity.HowManyMeet, Derivation.AComparisonRead.Counted> outer = counting;
        counting = new LinkedHashMap<>();
        try {
            return overQuantitiesCounting(left, right, states);
        } finally {
            counting = outer;
        }
    }

    /** The numbers of the input {@code forms} are over, which is what a comparison read through
     *  them names however much of it cancels. */
    private static Set<NumericTerm> ofTheInputIn(List<LinearForm<Quantity>> forms) {
        Set<NumericTerm> out = new LinkedHashSet<>();
        for (LinearForm<Quantity> form : forms) {
            for (Quantity atom : form.coefs().keySet()) {
                if (atom instanceof DecisionAtom.OfTheInput(NumericTerm term)) {
                    out.add(term);
                }
            }
        }
        return out;
    }

    private Derivation overQuantitiesCounting(Denotation left, Denotation right, Rel states) {
        List<LinearForm<Quantity>> sides = new ArrayList<>();
        for (Denotation side : List.of(left, right)) {
            switch (AffineForms.outcome(side.value(), side.at(), quantities())) {
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
        if (form.coefs().isEmpty()) {
            return new Derivation.ACutThatCutsNothing(states.holds(form.constant().signum()),
                    ofTheInputIn(sides));
        }
        return aRelation(Derivation.ComparisonReading.OVER_BOUND_VALUES, form, states, counting);
    }

    /** {@code form states 0}, read by {@code by}, written the one way every writing of a relation
     *  comes to ({@link Relation.OneWay}). */
    private static Derivation aRelation(Derivation.ComparisonReading by, LinearForm<Quantity> form,
                                        Rel states) {
        Relation.OneWay<Quantity> one = Relation.OneWay.of(form, states);
        return new Derivation.AComparisonRead(by,
                new Relation.Affine(one.form(), one.proposition()), one.holds());
    }

    /**
     * The same, holding how each count it names was read: the ones of {@code read} it still names —
     * a count written on both sides comes to nought and names none.
     */
    private static Derivation aRelation(Derivation.ComparisonReading by, LinearForm<Quantity> form,
                                        Rel states,
                                        Map<Quantity.HowManyMeet, Derivation.AComparisonRead.Counted>
                                                read) {
        Relation.OneWay<Quantity> one = Relation.OneWay.of(form, states);
        List<Derivation.AComparisonRead.Counted> named = new ArrayList<>();
        read.forEach((count, how) -> {
            if (one.form().coefs().containsKey(count)) {
                named.add(how);
            }
        });
        return new Derivation.AComparisonRead(by,
                new Relation.Affine(one.form(), one.proposition()), one.holds(), named);
    }

    /**
     * What this reading calls an atom of a number: a number of the input where the expression is
     * one, a number a dependency answered where the call is written, and otherwise a number of a
     * value the body bound, named by its binding and the fields read off it — an answer given a name
     * among them.
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
                return leafOf(node, at, null);
            }

            @Override
            public LinearForm<Quantity> leafOf(
                    Core node, InputReads at,
                    AffineForms.Outcome.StoppedAt<Quantity, InputReads> inside) {
                NumericTerm term = InputNumber.of(node, read.domain(), at, read.rules());
                if (term != null) {
                    return LinearForm.atom(new DecisionAtom.OfTheInput(term));
                }
                // How many an operation's answer holds, as its law says of its arguments.
                if (AnOperationApplied.of(Core.withoutStanding(node)) instanceof AnOperationApplied
                        measured && measured.operation() instanceof ValueName.Stdlib measure
                        && DefaultBoundOperationFacts.get().takenAs(measure)
                                instanceof TakenAs.HowManyItHolds
                        && measured.args().size() == 1) {
                    return sizeOf(measured.args().getFirst(), at)
                            instanceof Sized.AsAForm(LinearForm<Quantity> form) ? form : null;
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
                // A number a dependency answered, which a row stands in and so controls, named as
                // the decision table names it: the evaluation of the call, whether it is written
                // here or a name for it is.
                DecisionSubject.AnAnswer answered = answerAt(node, at);
                if (answered != null) {
                    return LinearForm.atom(new DecisionAtom.OfAnAnswer(answered));
                }
                if (!(under instanceof Core.Read name)) {
                    return null;
                }
                // A binding whose value turns on which application this is holds another value on
                // the next, and its name would name them alike.
                if (at.turnsOnAnApplication(name, read.rules().symbols(),
                        read.rules().newtypes())) {
                    return null;
                }
                return switch (at.meaningOf(name, read.rules().symbols(), read.rules().newtypes())) {
                    case ReadMeaning.Element _, ReadMeaning.OneOf _, ReadMeaning.Position _ -> null;
                    // A name given a choice between values holds whichever arm was taken, which
                    // is a number for each case and not one the body bound.
                    case ReadMeaning.Through(Denotation denotes)
                            when Choice.of(underItsAccesses(denotes).value()) != null -> null;
                    // A name read through to what it was given, which the reading stopped inside
                    // where it did: the value is named by its binding, and why its number is none
                    // of the input's goes with it.
                    case ReadMeaning.Through _ -> LinearForm.atom(new Quantity.OfABinding(
                            name.binding(), steps, node.type(),
                            Optional.ofNullable(inside).map(Pullback.this::noFormOf)));
                    case ReadMeaning.Unknown _ -> LinearForm.atom(new Quantity.OfABinding(
                            name.binding(), steps, node.type(), Optional.empty()));
                };
            }

            @Override
            public InputReads inside(Core.LetIn li, InputReads at) {
                return at.and(li.binder(), li.value());
            }

            @Override
            public AffineForms.ReadThrough<InputReads> readThrough(Core.Read name, InputReads at) {
                // A name given what a dependency answered is read through to the call, which is
                // the evaluation it names ({@link InputReads#answerAt}): the answer a row stands in
                // and a reader walking the tree relates by that evaluation.
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
     * A comparison of a truth a row controls against a truth written out, or null where it is no
     * such comparison.
     *
     * <p>A truth of the input as the reading of the input reads one, and one a dependency answered
     * as the decision table does: {@code known(name) == false} holding is {@code known(name)} not
     * holding, over either.
     */
    private Derivation truthCompared(StatedComparison comparison, InputReads reads) {
        InputTruth truth = InputTruth.compared(comparison, true, reads, read.rules().symbols(),
                read.rules().newtypes());
        if (truth != null) {
            return new Derivation.ATruthCompared(new DecisionSubject.AnInput(truth.at()),
                    truth.held());
        }
        return BooleanMeaning.againstATruth(comparison, true, read.rules().symbols(),
                        side -> subjects.isTheTruthOfAnAnswer(side, reads))
                .map(against -> subjects.truthOf(against.side(), against.held(), reads))
                .<Derivation>map(stood -> new Derivation.ATruthCompared(stood.condition().of(),
                        stood.held()))
                .orElse(null);
    }

    /**
     * A truth held against a truth the source settles, as that truth or its denial — or null where
     * neither side is a truth held against one written out.
     *
     * <p>Whatever the truth is: what it states is read as any truth is ({@link #observe}), through
     * a name, a denial or a choice by cases. The truth of a subject a row controls is read by the
     * rule before this one, which keeps the comparison as the part it is; this is every other.
     */
    private Derivation heldAgainstAWrittenTruth(StatedComparison stated, InputReads reads) {
        return BooleanMeaning.againstATruth(stated, true, read.rules().symbols(),
                        side -> BooleanMeaning.folded(side, read.rules().symbols()).isEmpty())
                .<Derivation>map(against -> new Derivation.HeldAgainstAWrittenTruth(
                        observe(against.side(), AnswerAspect.TRUTH, reads), against.held()))
                .orElse(null);
    }

    /**
     * The subject a row controls that {@code e} is the truth of: a position, or what a dependency
     * answered — or null where it is neither.
     */
    private DecisionSubject truthAt(Core e, InputReads reads) {
        TermPath position = InputTruth.positionOf(e, reads, read.rules().newtypes());
        return position != null ? new DecisionSubject.AnInput(position) : answerAt(e, reads);
    }

    /** What a dependency answered, or a place inside it, that {@code e} is — or null where it is
     *  no such thing. */
    private DecisionSubject.AnAnswer answerAt(Core e, InputReads reads) {
        return subjects.anAnswer(e, reads);
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
                yield aRelation(Derivation.ComparisonReading.AS_A_CUT,
                        asQuantities(DecisionComparison.ofTheInput(against)), states);
            }
            case AffineReading.OfAComparison.CutsNothing constant ->
                    new Derivation.ACutThatCutsNothing(
                            constant.holds(comparison.claim().statedRelation()), constant.read());
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
     * A comparison one side of which is a value chosen by cases, read as the choice: in each case,
     * the comparison of what that case answers — or null where neither side is such a value.
     *
     * <p>The cases are the language's — an {@code if}, a {@code match} — and the library's, where an
     * operation answers one of its arguments by how its arguments stand — the arms of one
     * {@link Choice} either way. What a case answers is compared with the other side
     * wherever each was read, so a case reached through a name given the choice is compared with a
     * side read where the comparison stands ({@link #overQuantities}).
     */
    private Derivation ofAChoice(StatedComparison stated, Denotation at, InputReads reads) {
        Denotation left = new Denotation(stated.left(), reads);
        Denotation right = new Denotation(stated.right(), reads);
        // What each case answers is related as a number ({@link #overQuantities}), so this takes
        // the comparisons of values counted on a carrier and no others. A truth held against one
        // written out is that truth, which a rule before this reads whatever chooses it.
        Carrier counted = Carrier.ofValue(Core.withoutStanding(stated.left()).type(),
                read.rules().declarations());
        if (counted == null || !counted.counts()
                || (chosenAt(left) == null && chosenAt(right) == null)) {
            return null;
        }
        // Each case of one side is compared with each of the other's, on every application this
        // reading is one of: counted before any is made.
        long most = READINGS.maximum();
        if (reads.readings() * readingsOf(left, most) * readingsOf(right, most) > most) {
            return partOf(at, new Derivation.Stopped(new WhyUnread.MoreReadingsThanAreMade(),
                    false));
        }
        return new Derivation.AComparisonOfAChoice(
                comparedCase(left, right, stated.claim().statedRelation(), at));
    }

    /**
     * {@code left states right}, each side split into its cases where it is chosen by them, and
     * related as numbers where neither is.
     */
    private Derivation comparedCase(Denotation left, Denotation right, Rel states,
                                    Denotation at) {
        Derivation byLeft = byItsCases(left, at, side -> comparedCase(side, right, states, at));
        if (byLeft != null) {
            return byLeft;
        }
        Derivation byRight = byItsCases(right, at, side -> comparedCase(left, side, states, at));
        return byRight != null ? byRight : partOf(at, overQuantities(left, right, states));
    }

    /**
     * How many comparisons {@code side} is split into where a comparison over it is read as its
     * cases ({@link #comparedCase}): one where it is chosen by none, and otherwise one for what
     * each case answers and one for each relation of the values a library operation's case is
     * reached under — or one more than {@code most}, where it is more than that.
     */
    private long readingsOf(Denotation side, long most) {
        Denotation chosen = chosenAt(side);
        if (chosen == null) {
            return 1;
        }
        Choice choice = Choice.of(Core.withoutStanding(chosen.value()));
        long readings = 0;
        for (Choice.Arm arm : choice.arms()) {
            InputReads inside = chosen.at().choosing(arm.decidedBy(), read.rules().symbols(),
                    read.rules().newtypes());
            readings += readingsOf(new Denotation(arm.answers(), inside), most);
            List<Choice.ArgumentRelation> reachedUnder = switch (choice.kind()) {
                case THE_ARGUMENTS -> relationsDeciding(arm);
                // An arm a condition or a case decides is reached by reading that once, and not
                // by comparisons split on its own.
                case A_CONDITION, A_CASE, AN_ATTEMPT -> List.of();
            };
            for (Choice.ArgumentRelation stands : reachedUnder) {
                readings += readingsOf(new Denotation(stands.left(), inside), most)
                        * readingsOf(new Denotation(stands.right(), inside), most);
            }
            if (readings > most) {
                return most + 1;
            }
        }
        return readings;
    }

    /**
     * The value {@code side} stands for, where it is chosen by cases — or null where it is not.
     */
    private Denotation chosenAt(Denotation side) {
        Denotation stands = side.at().standing(side.value(), read.rules().symbols(),
                read.rules().newtypes());
        Choice choice = Choice.of(Core.withoutStanding(stands.value()));
        if (choice == null) {
            return null;
        }
        return switch (choice.kind()) {
            case A_CONDITION, A_CASE -> stands;
            // A case is about values the call was given, and one it was not given is no value to
            // compare.
            case THE_ARGUMENTS -> choice.arms().stream().allMatch(arm -> arm.answers() != null
                    && relationsDeciding(arm).stream().allMatch(
                            each -> each.left() != null && each.right() != null))
                    ? stands : null;
            case AN_ATTEMPT -> stands;
        };
    }

    /**
     * The choice {@code side} is, with {@code compared} read of what each case answers — or null
     * where {@code side} is chosen by no cases.
     *
     * @param at the comparison the choice is a side of, where it is a part of a larger condition:
     *           how the arguments of an operation stand is a part read off it
     */
    private Derivation byItsCases(Denotation side, Denotation at,
                                  Function<Denotation, Derivation> compared) {
        Denotation chosen = chosenAt(side);
        if (chosen == null) {
            return null;
        }
        InputReads where = chosen.at();
        return switch (Core.withoutStanding(chosen.value())) {
            case Core.If iff -> new Derivation.IfThenElse(
                    observe(iff.cond(), AnswerAspect.TRUTH, where),
                    compared.apply(new Denotation(iff.then(), where)),
                    compared.apply(new Denotation(iff.els(), where)));
            case Core.Match match -> armsOf(match, where,
                    (body, inside) -> compared.apply(new Denotation(body, inside)));
            case Core.IfConstructed attempt -> {
                List<Derivation> taken = attempted(attempt, where);
                List<Choice.Arm> arms = Choice.of(attempt).arms();
                List<Derivation.MatchArms.Arm> out = new ArrayList<>();
                for (int i = 0; i < arms.size(); i++) {
                    InputReads inside = where.choosing(arms.get(i).decidedBy(),
                            read.rules().symbols(), read.rules().newtypes());
                    out.add(new Derivation.MatchArms.Arm(taken.get(i),
                            compared.apply(new Denotation(arms.get(i).answers(), inside))));
                }
                yield new Derivation.MatchArms(out);
            }
            case Core e -> ofAnOperationsCases(e, Choice.of(e), where, at, compared);
        };
    }

    /**
     * The cases the library writes the definition of the operation {@code call} applies in, as the
     * arms of its choice ({@link Choice}): each reached where the values the call was given stand as
     * the case says and none before it does, with {@code compared} read of the value that case
     * answers.
     */
    private Derivation ofAnOperationsCases(Core call, Choice choice, InputReads where,
                                           Denotation at,
                                           Function<Denotation, Derivation> compared) {
        if (!(AnOperationApplied.of(call) instanceof AnOperationApplied applied
                && applied.operation() instanceof ValueName.Stdlib operation)) {
            return null;
        }
        List<Derivation.MatchArms.Arm> cases = new ArrayList<>();
        for (Choice.Arm arm : choice.arms()) {
            Derivation reached = null;
            for (Choice.ArgumentRelation stands : relationsDeciding(arm)) {
                Derivation one = comparedCase(new Denotation(stands.left(), where),
                        new Denotation(stands.right(), where), stands.rel(), at);
                reached = reached == null ? one
                        : new Derivation.Joined(ConditionJoin.BOTH, reached, one);
            }
            if (reached == null) {
                // A case reached whatever the arguments are is no case of a choice, and the cases
                // after it would never be reached; the library writes none.
                throw new IllegalStateException("a case of " + operation + " is reached by no"
                        + " standing of its arguments");
            }
            cases.add(new Derivation.MatchArms.Arm(reached,
                    compared.apply(new Denotation(arm.answers(), where))));
        }
        return new Derivation.AnOperationsCases(operation, cases);
    }

    /**
     * How the values a call was given stand where {@code arm} of the case the library defines it in
     * is taken. Every way an arm is decided is named: a call is chosen by its values standing, and
     * an arm decided any other way is no arm of one.
     */
    private static List<Choice.ArgumentRelation> relationsDeciding(Choice.Arm arm) {
        return switch (arm.decidedBy()) {
            case Choice.Decides.ByArgumentRelations by -> by.relations();
            case Choice.Decides.ACondition other -> noArmOfACall(other);
            case Choice.Decides.ACase other -> noArmOfACall(other);
            case Choice.Decides.ItWasBuilt other -> noArmOfACall(other);
            case Choice.Decides.ItDeparted other -> noArmOfACall(other);
        };
    }

    private static List<Choice.ArgumentRelation> noArmOfACall(Choice.Decides decidedBy) {
        throw new IllegalStateException("a call is chosen by how the values it was given stand,"
                + " and " + decidedBy + " is not that");
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
    static final class Once<T> implements Supplier<T> {

        private final Supplier<T> making;
        private T made;

        Once(Supplier<T> making) {
            this.making = making;
        }

        @Override
        public T get() {
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
    private static WhyUnread unreadAs(AnOperationApplied applied, AnswerAspect aspect,
                                      InputReads reads) {
        if (applied == null) {
            return new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT);
        }
        return switch (applied.operation()) {
            case ValueName.Stdlib operation -> new WhyUnread.NoLawFor(operation, aspect);
            case ValueName.Behavior behavior -> aspect == AnswerAspect.EMPTINESS
                    ? new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT)
                    : whatABehaviorAnswers(behavior, reads);
            case ValueName.Helper _ -> new WhyUnread.WhatARecursiveHelperAnswers();
            default -> new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT);
        };
    }

    /**
     * Why what {@code behavior} answered was read as nothing: a dependency's answer is named by what
     * it was asked about, so one of them unread is one asked about a value nothing names yet, and
     * any other behavior's is what its body computes.
     */
    private static WhyUnread whatABehaviorAnswers(ValueName.Behavior behavior, InputReads reads) {
        return new WhyUnread.NotYetComposed(reads.standsIn(behavior)
                ? WhyUnread.NotYetComposed.Step.A_DEPENDENCY_ASKED_ABOUT_A_COMPUTED_VALUE
                : WhyUnread.NotYetComposed.Step.A_BEHAVIOR_CALLED_BY_NAME);
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
     * What {@code value} takes a part of: what it stands as through the names and bindings it is
     * reached by ({@link InputReads#standing}), and then what each access that takes a part of a
     * value is of, as far as they go.
     *
     * <p>Where a reading has no rule for a value, what stopped it is what stands there, however the
     * value was spelled on the way to it. Beside {@link #chosenAt}, which stops at the first access:
     * a comparison is split into the cases of what it compares, which through an access it cannot
     * yet be.
     */
    private Denotation underItsAccesses(Denotation value) {
        Denotation at = value;
        while (true) {
            Denotation stands = at.at().standing(Core.withoutStanding(at.value()),
                    read.rules().symbols(), read.rules().newtypes());
            Core e = Core.withoutStanding(stands.value());
            Core whole = switch (e) {
                case Core.FieldProjection projection -> projection.lastAccess();
                case Core.FieldAccess access -> access.target();
                case Core.TupleGet get -> get.tuple();
                default -> null;
            };
            if (whole == null) {
                return new Denotation(e, stands.at());
            }
            at = new Denotation(whole, stands.at());
        }
    }

    /**
     * Why an expression the arithmetic has no rule for, read in {@code reads}, is no number of the
     * input: what stands at the end of the accesses it is made of.
     */
    private WhyUnread noRuleFor(Core stopped, InputReads reads) {
        Denotation end = underItsAccesses(new Denotation(stopped, reads));
        Core e = Core.withoutStanding(end.value());
        InputReads in = end.at();
        if (e instanceof Core.Read name) {
            return switch (in.meaningOf(name, read.rules().symbols(), read.rules().newtypes())) {
                case ReadMeaning.Element _ ->
                        new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.CONTAINER);
                case ReadMeaning.OneOf _ -> new WhyUnread.NotYetComposed(
                        WhyUnread.NotYetComposed.Step.VALUES_WRITTEN_OUT);
                // A name read through is followed above to what it was given, so one that stands
                // here came round to itself.
                case ReadMeaning.Through _, ReadMeaning.Unknown _, ReadMeaning.Position _ ->
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
            case ValueName.Behavior behavior -> whatABehaviorAnswers(behavior, in);
            case ValueName.Helper _ -> new WhyUnread.WhatARecursiveHelperAnswers();
            case ValueName.Stdlib operation -> {
                if (!facts.isDefinedByCases(operation).isEmpty()) {
                    yield new WhyUnread.NotYetComposed(
                            WhyUnread.NotYetComposed.Step.A_CHOICE_BY_CASES);
                }
                if (facts.takenAs(operation) != null && !applied.args().isEmpty()) {
                    yield noNumberOf(operation, applied.args().getFirst(), in);
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
        // Read again for why: the arithmetic says only that nothing named the size, and what
        // stopped the reading of it is the reading's to say.
        if (DefaultBoundOperationFacts.get().takenAs(measure) instanceof TakenAs.HowManyItHolds
                && sizeOf(measured, reads) instanceof Sized.NotSized(WhyUnread why)) {
            return why;
        }
        Core made = Core.withoutStanding(reads.standing(measured, read.rules().symbols(),
                read.rules().newtypes()).value());
        if (!(AnOperationApplied.of(made) instanceof AnOperationApplied applied
                && applied.operation() instanceof ValueName.Stdlib madeBy)) {
            return new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT);
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
