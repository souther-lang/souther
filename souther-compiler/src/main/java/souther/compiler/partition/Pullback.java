package souther.compiler.partition;

import net.unit8.notation199x.pattern.CodePoints;

import souther.compiler.check.ARecursion;
import souther.compiler.check.AffineForms;
import souther.compiler.check.ValueStanding;
import souther.compiler.check.AnOperationApplied;
import souther.compiler.check.BooleanMeaning;
import souther.compiler.check.CalledBody;
import souther.compiler.check.Carrier;
import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.Choice;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.ConstantComparison;
import souther.compiler.check.ClauseName;
import souther.compiler.check.ClausesInOrder;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.KeyedAccumulation;
import souther.compiler.check.Location;
import souther.compiler.check.NonAffineOperation;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.RecursionOverAList;
import souther.compiler.check.RecursionOverATree;
import souther.compiler.check.RemainderOfAShiftedValue;
import souther.compiler.check.SeededWalk;
import souther.compiler.check.StatedComparison;
import souther.compiler.check.StringPredicates;
import souther.compiler.check.Symbols;
import souther.compiler.check.TheSignOfAnOrder;
import souther.compiler.check.WholeUnitsBetween;
import souther.compiler.core.Core;
import souther.compiler.core.WhatABodyReads;
import souther.compiler.check.AnIndexedMap;
import souther.compiler.inputs.AnIdentityMap;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.ElementsMet;
import souther.compiler.inputs.InputNumber;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.InputTruth;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.WrittenOutElements;
import souther.compiler.meaning.Conclusion;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.Derivation.ALawJoinsWithoutWhatImpliesAnother.Disjunct;
import souther.compiler.meaning.MeaningsOfABody.Meaning;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.TruthTable;
import souther.compiler.meaning.WhichCase;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.meaning.WrittenOfANode;
import souther.compiler.meaning.ACarriedValue;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.semantics.ElementLineage;
import souther.compiler.semantics.LawArguments;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.SideAnswered;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.semantics.TakenAs;
import souther.compiler.semantics.Unsayable;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.time.LocalDate;
import java.time.Year;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.OptionalInt;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.function.UnaryOperator;

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
    private final Set<DecisionSubject> quantifying = new HashSet<>();
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
    /**
     * The counts every element settles alike that the law's comparison being read needed, as they
     * are read ({@link Derivation.ALawComparison#alike}) — or null where what is read is no law's
     * comparison.
     */
    private List<Derivation.AComparisonRead.Counted> alike;
    /**
     * The elements of the containers the comparison being read is read of, which name stands for
     * each — held to one name for each container ({@link ElementsMet}). Nothing where what is read
     * is no comparison of two numbers.
     */
    private ElementsMet elementsMet = ElementsMet.NONE;
    /**
     * How many each answer an operation sized by cases holds, in the case of it the comparison
     * being read is read in ({@link #inEachCaseOf}): a number of the input, where the arguments
     * stand as that case says.
     */
    private final Map<Core, LinearForm<Quantity>> sizedInACase = new HashMap<>();
    /**
     * What each walk whose step is being read carried into it, on the side its end is asked about
     * ({@link #acrossAWalk}).
     */
    private final Map<BindingId, Carried> carried = new HashMap<>();
    /**
     * What each call a recursion whose body is being read makes of itself is supposed to answer, on
     * the side the recursion is asked about ({@link #acrossARecursion}). By the call, since another
     * call of the same helper is not a step of this one.
     */
    private final Map<Core, Supposed> recursed = new IdentityHashMap<>();
    /**
     * The recursions whose body is being read. One reached again inside its own body through
     * another helper is a recursion through two, which is read as neither.
     */
    private final Set<ValueName.Helper> recursing = new HashSet<>();

    /** What a value a walk or a recursion hands back to itself is supposed to be. */
    private sealed interface Supposed permits Carried, Descending, Reaching {}

    /** What a walk carried, on {@code aspect}: {@code value}, which each way of concluding the
     *  step supposes ({@link Derivation.Supposing}). */
    private record Carried(AnswerAspect aspect, ACarriedValue value) implements Supposed {}

    /**
     * A call a search from the node at {@code from} makes of itself, standing on {@code aspect}
     * for {@code value} where it is on a node below, with the field it went down through put into
     * {@code through}.
     */
    private record Descending(AnswerAspect aspect, int node, TermPath from, ACarriedValue value,
                              Set<String> through) implements Supposed {}

    /**
     * A call a search from the node at {@code from} makes of itself, standing for the search from
     * the node it is on where that is below, down {@code through} ({@link Derivation.AReachedNode}).
     */
    private record Reaching(AnswerAspect aspect, int node, TermPath from, List<String> through,
                            Derivation atANode, ConditionJoin how) implements Supposed {}

    private Pullback(InputReading read, Optional<ModelOccurrence> where) {
        this.read = read;
        this.where = where;
        this.subjects = new DecisionSubjects(read.domain(), read.rules().symbols(),
                read.rules().declarations(), read.rules().newtypes(), KeptTruths.readIn(read));
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

    /** What {@code optional} holding a value states. */
    static Pulled ofAPresence(Core optional, InputReads reads, InputReading read,
                              Optional<ModelOccurrence> where) {
        Pullback reading = new Pullback(read, where);
        return reading.pulled(reading.observe(optional, AnswerAspect.PRESENCE, reads));
    }

    /**
     * What a comparison the source wrote states, read as any truth is: a size held where it parts
     * nought from every size above it is whether the container holds anything.
     */
    static Pulled ofAComparison(StatedComparison comparison, InputReads reads, InputReading read,
                                Optional<ModelOccurrence> where) {
        Pullback reading = new Pullback(read, where);
        return reading.pulled(reading.underTheEntriesLookedUp(
                reading.comparison(comparison, null, false, reads), comparison, reads));
    }

    /**
     * {@code about}, with what picked out each entry it states something of: a lookup answers one
     * entry, and a statement about its value is about that one.
     */
    private Derivation underTheEntriesLookedUp(Derivation about, StatedComparison comparison,
                                               InputReads reads) {
        Map<BindingId, InputReads.EntryLookedUp> entries = reads.entriesLookedUp();
        if (entries.isEmpty()) {
            return about;
        }
        // The entries of the names the comparison is written through, and not of every name in
        // force: two names for two entries of one map are one position, and which of them a
        // number is a number of is the name it was written with.
        Set<BindingId> written = ElementsMet.namesOfElementsIn(
                List.of(comparison.left(), comparison.right()), reads, read.rules().newtypes());
        Derivation out = about;
        for (Map.Entry<BindingId, InputReads.EntryLookedUp> each : entries.entrySet()) {
            if (!written.contains(each.getKey())) {
                continue;
            }
            Derivation picked = observe(each.getValue().lookup(), AnswerAspect.PRESENCE, reads);
            // A lookup whose key no position holds says nothing of which entry it is, and a
            // statement about an entry it does not pick out is about another.
            if (!(picked.concludes(Optional.empty()) instanceof Proposition.Some some
                    && some.holds())) {
                WhyUnread stopped = Proposition.firstStopIn(picked.concludes(Optional.empty()));
                return new Derivation.Stopped(stopped != null ? stopped
                        : new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT),
                        false);
            }
            out = new Derivation.OfTheEntryUnderTheKey(picked, out);
        }
        return out;
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
        return new OnTheInput(reading.pulled(reading.underTheEntriesLookedUp(
                reading.firstThatReadsIt(
                        reading.rulesFor(comparison, null, false, reads, arithmetic)),
                comparison, reads)),
                arithmetic);
    }

    /**
     * Whether what a written comparison states was carried past it to the input — so that what it
     * states is the parts it was carried to, and not a rule the comparison draws of its own.
     *
     * <p>Only an emptiness check is carried anywhere: any other comparison is the relation it
     * states. And one is carried past only where the container it asks about is no position of its
     * own and every part it was carried to was read — one that stopped on the way is a rule about a
     * value made from the input, which the comparison still is.
     *
     * <p>And not where what it states is relations — beside what a row answers of its own values,
     * if anything — some of which nothing else written there states. Those are lines, and the
     * check draws them: {@code List.isEmpty(List.take(n, xs))}
     * holds where {@code n} is below one or {@code xs} is empty, and neither is a comparison
     * anybody wrote. Relations every one of which was read off a comparison written inside it are
     * that comparison's lines, as {@code List.isEmpty(List.filter(x -> x > 5, [a, b]))} is the
     * closure's on each value.
     *
     * @param check the node the check is written as
     */
    static boolean carriesPast(StatedComparison comparison, Core check, InputReads reads,
                               InputReading read) {
        return mayBeCarriedPast(comparison)
                && carriesPast(ofAComparison(comparison, reads, read, Optional.empty()), check);
    }

    /** The same, of what an emptiness check written as {@code check} was read to state. */
    static boolean carriesPast(Pulled read, Core check) {
        // Unread anywhere in what is stated, and not among the parts it turns on: a part nothing
        // read that is the same on every run turns on nothing, and is still not read.
        Proposition stated = read.proposition();
        if (Proposition.leavesSomethingUnread(stated)) {
            return false;
        }
        // Values of the input stood against one another are a relation the check itself states,
        // unless something written inside it states it: a call answering a truth reads its own
        // relation, and the operation an emptiness check was carried through answers a set.
        if (Cutting.valuesItRelates(stated) != null) {
            return read.turnsOn().stream()
                    .allMatch(leaf -> aTruthStatedWhereItIsWritten(leaf.from().value(), check));
        }
        return (!Cutting.onlyRelations(stated) && !Cutting.drawsLines(stated))
                || read.turnsOn().stream()
                        .allMatch(leaf -> aComparisonWrittenInside(leaf.from().value(), check));
    }

    /** Whether {@code from} is a comparison or a call answering a truth, written inside
     *  {@code check}, which states its own relation. */
    private static boolean aTruthStatedWhereItIsWritten(Core from, Core check) {
        Core node = Core.withoutStanding(from);
        return aComparisonWrittenInside(from, check)
                || (node != Core.withoutStanding(check) && node instanceof Core.PreservedCall call
                        && Type.BOOL.equals(call.type()));
    }

    /** Whether {@code from} is a comparison written inside {@code check}, which draws its own
     *  lines. */
    private static boolean aComparisonWrittenInside(Core from, Core check) {
        Core node = Core.withoutStanding(from);
        return node != Core.withoutStanding(check) && node instanceof Core.Binary
                && BooleanMeaning.asAComparison(node).isPresent();
    }

    /**
     * Whether {@code comparison} is one {@link #carriesPast} can answer yes for, which is a question
     * about its shape alone: only an emptiness check is carried anywhere.
     */
    static boolean mayBeCarriedPast(StatedComparison comparison) {
        return AnEmptinessCheck.checked(comparison) != null;
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
        return observe(standing, new Asked.OnASide(aspect), reads);
    }

    /**
     * What is asked of a value, read wherever the value is made: through the binding or name that
     * stands for it and into each arm of the choice that answers it, the same way whatever is asked.
     * A value made by none of those is asked by what is asked of it.
     */
    private sealed interface Asked {

        /** How the value comes out on one side: holding, holding something, holding a value. */
        record OnASide(AnswerAspect aspect) implements Asked {}

        /**
         * Whether some element of the value, a container, meets {@code some}, which a law {@code
         * law} is being read at a call states of the container the call was handed.
         */
        record SomeElement(ALawRead law, LawProposition.SomeElement<DeclaredArgument> some)
                implements Asked {}
    }

    /** How {@code standing} answers {@code asked}, read where the value is made. */
    private Derivation observe(Core standing, Asked asked, InputReads reads) {
        Core e = Core.withoutStanding(standing);
        // What a walk carried, or a recursion's call answered, stands for how it came out on one
        // side, and for nothing else asked of it.
        AnswerAspect side = asked instanceof Asked.OnASide(AnswerAspect aspect) ? aspect : null;
        switch (e) {
            case Core.Read name when carried.get(name.binding()) instanceof Carried supposed -> {
                return supposed.aspect() == side
                        ? new Derivation.WhatAWalkCarried(supposed.value())
                        : unread(e, reads,
                                new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT));
            }
            case Core.Call call when recursed.get(call) instanceof Supposed supposed -> {
                Derivation answered = side == null ? null : supposedOf(call, supposed, side, reads);
                return answered != null ? answered : unread(e, reads,
                        new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT));
            }
            case Core.LetIn let -> {
                return new Derivation.ThroughABinding(
                        observe(let.body(), asked, reads.and(let.binder(), let.value())));
            }
            case Core.Read name when reads.meaningOf(name, read.rules().symbols(),
                    read.rules().newtypes()) instanceof ReadMeaning.Through through -> {
                return new Derivation.ThroughABinding(
                        observe(through.denotes().value(), asked, through.denotes().at()));
            }
            case Core.If iff -> {
                Derivation cond = observe(iff.cond(), AnswerAspect.TRUTH, reads);
                Derivation then = observe(iff.then(), asked, reads);
                return new Derivation.IfThenElse(cond, then, observe(iff.els(), asked, reads));
            }
            case Core.Match match -> {
                return armsOf(match, reads, (body, inside) -> observe(body, asked, inside));
            }
            default -> { }
        }
        return switch (asked) {
            case Asked.OnASide(AnswerAspect aspect) -> switch (aspect) {
                case TRUTH -> truth(e, reads);
                case EMPTINESS -> holdingSomething(e, reads);
                case PRESENCE -> present(e, reads);
            };
            case Asked.SomeElement(ALawRead law, var some) ->
                    law.someElementOf(new Denotation(e, reads), some);
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
                () -> writtenOut(e, AnswerAspect.TRUTH, reads),
                () -> ofAnElementOfAnAnswer(e, AnswerAspect.TRUTH, reads),
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
                () -> applied == null ? null
                        : new ALawRead(applied, e, reads).aCharacterInAClass(),
                () -> byALaw(applied, e, AnswerAspect.TRUTH, reads, new Denotation(e, reads)),
                () -> acrossAWalk(e, AnswerAspect.TRUTH, reads),
                () -> acrossARecursion(e, AnswerAspect.TRUTH, reads),
                () -> inTheCalledBody(e, new Asked.OnASide(AnswerAspect.TRUTH), reads)));
        return taken != null ? taken
                : unread(e, reads, unreadAs(applied, AnswerAspect.TRUTH, reads));
    }

    /**
     * What a value the source wrote out answers about {@code aspect}, where {@code e} is one or
     * stands as one — or null where it is neither.
     *
     * <p>Stands as one through what a reading of it here follows: a field of a construction written
     * out, which is what an element a filter or a closure is handed holds. {@code x.keep} over an
     * element written {@code Item { keep = false, .. }} is false on every row. A name was followed
     * before this was asked ({@link #observe}), so only a field is followed here.
     */
    private Derivation writtenOut(Core e, AnswerAspect aspect, InputReads reads) {
        Derivation written = writtenOut(e, aspect);
        if (written != null || !(Core.withoutStanding(e) instanceof Core.FieldAccess
                || Core.withoutStanding(e) instanceof Core.FieldProjection)) {
            return written;
        }
        return writtenOut(reads.standing(e, read.rules().symbols(), read.rules().newtypes())
                .value(), aspect);
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

    /**
     * How {@code e}, a name for an element a walk was handed from what an operation answered, comes
     * out on {@code aspect}, where every element of that answer comes out on that side
     * ({@link Derivation.OfAnElementOfAnAnswer}) — or null where it is no such name.
     */
    private Derivation ofAnElementOfAnAnswer(Core e, AnswerAspect aspect, InputReads reads) {
        Core container = reads.containerOfTheElement(e);
        AnOperationApplied made = container == null ? null : AnOperationApplied.of(reads.standing(
                container, read.rules().symbols(), read.rules().newtypes()).value());
        SideAnswered side = made == null ? null
                : DefaultBoundOperationFacts.get().everyElementOfItsAnswerIs(made.operation());
        return side == null || side.aspect() != aspect ? null
                : new Derivation.OfAnElementOfAnAnswer(made.operation(), side);
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
        return new Once<>(() -> AffineReading.read(stated, reads, read));
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
                () -> partOf(at, ofTwoValuesWrittenOut(stated, reads)),
                () -> partOf(at, asACut(stated, arithmetic.get(), fixed)),
                () -> partOf(at, onAnOrder(stated, arithmetic.get(), reads)),
                () -> ofTheYearOfADate(stated, at, fixed, reads),
                () -> ofACountOfWholeUnits(stated, at, fixed, reads),
                () -> ofAShiftedRemainder(stated, at, fixed, reads),
                () -> partOf(at, ofARemainderOfAForm(stated, reads)),
                () -> partOf(at, ofItsArguments(stated, fixed, reads)),
                () -> ofASizeInCases(stated, at, reads),
                () -> ofAChoice(stated, at, reads),
                () -> throughWhatItStopsAt(stated, at, fixed, reads),
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
                () -> writtenOut(e, AnswerAspect.EMPTINESS, reads),
                () -> ofAnElementOfAnAnswer(e, AnswerAspect.EMPTINESS, reads),
                () -> byALaw(applied, e, AnswerAspect.EMPTINESS, reads, asked),
                () -> acrossAWalk(e, AnswerAspect.EMPTINESS, reads),
                () -> acrossARecursion(e, AnswerAspect.EMPTINESS, reads),
                () -> inTheCalledBody(e, new Asked.OnASide(AnswerAspect.EMPTINESS), reads),
                () -> {
                    DecisionSubject held = reads.pathOf(e, read.rules().newtypes())
                            instanceof PathResolution.At(TermPath at)
                            ? new DecisionSubject.AnInput(at) : answerAt(e, reads);
                    if (held == null) {
                        return null;
                    }
                    Derivation some = holdsSomethingAt(held, e.type());
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
                () -> writtenOut(e, AnswerAspect.PRESENCE, reads),
                () -> ofAnElementOfAnAnswer(e, AnswerAspect.PRESENCE, reads),
                () -> byALaw(applied, e, AnswerAspect.PRESENCE, reads, new Denotation(e, reads)),
                () -> acrossAWalk(e, AnswerAspect.PRESENCE, reads),
                () -> acrossARecursion(e, AnswerAspect.PRESENCE, reads),
                () -> inTheCalledBody(e, new Asked.OnASide(AnswerAspect.PRESENCE), reads),
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
     * The position of the input whose holding something is what the container {@code container}
     * holding something comes to, or empty where there is none.
     *
     * <p>A container at a position of the input is that position. A map built by filing a counter
     * under the key of each element of a list ({@link KeyedAccumulation}) has an entry for each
     * element, so it holds something exactly where the list does. Any other container — a filter
     * of one, say — may be empty with what it was made of not, and is not read back to it.
     */
    static Optional<TermPath> positionHoldingWhatItHolds(Denotation container,
                                                         InputReading read) {
        Symbols symbols = read.rules().symbols();
        DeclarationNewtypes newtypes = read.rules().newtypes();
        if (container.at().pathOf(container.value(), newtypes) instanceof PathResolution.At(
                TermPath at)) {
            return Optional.of(at);
        }
        Denotation whole = container.at().standing(container.value(), symbols, newtypes);
        KeyedAccumulation filed = KeyedAccumulation.of(whole.value(), closure ->
                Core.withoutStanding(whole.at().standing(closure, symbols, newtypes).value())
                        instanceof Core.Block block ? block : null);
        if (filed == null) {
            return Optional.empty();
        }
        Denotation walked = whole.at().standing(filed.walked(), symbols, newtypes);
        return walked.at().pathOf(walked.value(), newtypes) instanceof PathResolution.At(
                TermPath at) ? Optional.of(at) : Optional.empty();
    }

    /**
     * {@code block}'s body read on each of its applications in {@code at}, held to how many readings
     * of one condition are made, each handed an occurrence there on some row ({@link KeptTruths}) —
     * for every reader of a closure over values written out.
     */
    static InputReads.Applications applicationsOf(Core.Block block, InputReads at,
                                                  InputReading read) {
        return at.applicationsOf(block, read.rules().symbols(), read.rules().newtypes(),
                READINGS.maximum(), KeptTruths.readIn(read));
    }

    /** The one of {@code rules} an expression is read by ({@link RuleChoice}). */
    private Derivation firstThatReadsIt(List<Supplier<Derivation>> rules) {
        return RuleChoice.firstThatReadsIt(rules, met, trying);
    }

    /**
     * Some arm of {@code match} taken, and what {@code states} reads of that arm's body where it is
     * taken — for a match a condition is, and for one that chooses a value a condition compares.
     *
     * <p>An arm is taken where the value is one of its cases and none of an arm before it. Which
     * cases a value written in the source is is settled before any row ({@link
     * InputReads#whetherEveryRowTakes}); one a row controls is a case the row writes at its position
     * or stands the dependency in with.
     */
    private Derivation.MatchArms armsOf(Core.Match match, InputReads reads,
                                        BiFunction<Core, InputReads, Derivation> states) {
        List<Derivation> selections = selectionsOf(match, reads);
        boolean ofAnEntry = reads.holdsAnEntryLookedUp(match.scrutinee(),
                read.rules().symbols(), read.rules().newtypes());
        List<Derivation.MatchArms.Arm> arms = new ArrayList<>();
        for (int i = 0; i < match.cases().size(); i++) {
            Core.Case arm = match.cases().get(i);
            InputReads inside = reads.choosing(Choice.Decides.ofCase(match, arm),
                    read.rules().symbols(), read.rules().newtypes());
            arms.add(new Derivation.MatchArms.Arm(selections.get(i),
                    states.apply(arm.body(), inside),
                    ofAnEntry && arm.binding() instanceof Core.ArmBinding.Payload));
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
        WhichCase scrutinee = null;
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
            } else if (presenceSelected(arm) != null) {
                // An optional is of its present case exactly where it holds a value, which is the
                // observation the reading has a rule for whatever made the optional.
                out.add(new Derivation.UnderADenial(
                        observe(match.scrutinee(), AnswerAspect.PRESENCE, reads),
                        !presenceSelected(arm)));
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

    /**
     * Whether {@code arm} selects an optional where it holds a value — true for its present case
     * alone, false for its absent case alone — or null where it selects by something else, or by
     * both.
     */
    private static Boolean presenceSelected(Core.Case arm) {
        boolean some = arm.pattern().takes(TypeSymbol.SOME);
        boolean none = arm.pattern().takes(TypeSymbol.NONE);
        return some == none ? null : some;
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
    private static Derivation selecting(WhichCase answered, Core.Case arm) {
        return switch (answered) {
            // One of several values the source wrote out, each of which may take another arm.
            case WhichCase.Written(var cases) ->
                    InputReads.whetherEveryRowTakes(arm, cases)
                            .<Derivation>map(Derivation.CasesWrittenOut::new)
                            .orElseGet(() -> new Derivation.Stopped(new WhyUnread.AtNoPosition(
                                    WhyUnread.AtNoPosition.Place.SCRUTINEE), false));
            case WhichCase.AtAnInput(TermPath at) -> new Derivation.CasesOfASubject(
                    new DecisionSubject.AnInput(at), CasesLeft.selectedBy(arm.pattern()));
            case WhichCase.AtAnAnswer(var answer) -> new Derivation.CasesOfASubject(
                    answer, CasesLeft.selectedBy(arm.pattern()));
            case WhichCase.Unread(WhyUnread why) -> new Derivation.Stopped(why, false);
            case WhichCase.ByItsArms(var arms) ->
                    new Derivation.OneOfItsArms(arms.stream().map(each ->
                            new Derivation.MatchArms.Arm(each.reached(),
                                    selecting(each.answers(), arm))).toList());
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
    private WhichCase answered(Denotation value,
                                              WhyUnread.AtNoPosition.Place nowhere) {
        Denotation chosen = chosenAt(value);
        if (chosen != null) {
            long most = READINGS.maximum();
            if (value.at().readings() * readingsOf(value, most) > most) {
                return new WhichCase.Unread(new WhyUnread.MoreReadingsThanAreMade());
            }
            return answeredByItsArms(chosen, nowhere);
        }
        Set<TypeSymbol> written = value.at().casesWritten(value.value(), read.rules().symbols(),
                read.rules().newtypes());
        if (written != null && !written.isEmpty()) {
            return new WhichCase.Written(written);
        }
        if (value.at().pathOf(value.value(), read.rules().newtypes())
                instanceof PathResolution.At(TermPath at)) {
            return new WhichCase.AtAnInput(at);
        }
        DecisionSubject.AnAnswer answer = answerAt(value.value(), value.at());
        if (answer != null) {
            return new WhichCase.AtAnAnswer(answer);
        }
        WhichCase called = calledFor(value, nowhere);
        // Made of nothing followed back to the input: what an operation answers, or a value the
        // source works out.
        return called != null ? called : new WhichCase.Unread(
                new WhyUnread.AtNoPosition(nowhere));
    }

    /** {@code chosen}'s arms, each reached where a run takes it and answering what it does. */
    private WhichCase answeredByItsArms(Denotation chosen,
                                                       WhyUnread.AtNoPosition.Place nowhere) {
        InputReads where = chosen.at();
        List<WhichCase.Arm> arms = new ArrayList<>();
        switch (Core.withoutStanding(chosen.value())) {
            case Core.If iff -> {
                Derivation cond = observe(iff.cond(), AnswerAspect.TRUTH, where);
                arms.add(new WhichCase.Arm(cond,
                        answered(new Denotation(iff.then(), where), nowhere)));
                arms.add(new WhichCase.Arm(new Derivation.UnderADenial(cond, true),
                        answered(new Denotation(iff.els(), where), nowhere)));
            }
            case Core.Match match -> {
                List<Derivation> selections = selectionsOf(match, where);
                for (int i = 0; i < match.cases().size(); i++) {
                    Core.Case arm = match.cases().get(i);
                    InputReads inside = where.choosing(Choice.Decides.ofCase(match, arm),
                            read.rules().symbols(), read.rules().newtypes());
                    arms.add(new WhichCase.Arm(
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
                    arms.add(new WhichCase.Arm(taken.get(i),
                            answered(new Denotation(choice.get(i).answers(), inside), nowhere)));
                }
            }
            // An operation of the library answering one of its arguments by how they stand: each
            // case reached where they stand as it says and no case before it does, and answering
            // what that argument is.
            case Core call -> {
                List<Choice.Arm> cases = Choice.of(call).arms();
                List<Derivation> stand = new ArrayList<>();
                for (Choice.Arm arm : cases) {
                    stand.add(howTheArgumentsStand(arm, where, chosen));
                }
                for (int i = 0; i < cases.size(); i++) {
                    arms.add(new WhichCase.Arm(
                            new Derivation.AnArmTaken(stand.subList(0, i), stand.get(i)),
                            answered(new Denotation(cases.get(i).answers(), where), nowhere)));
                }
            }
        }
        return new WhichCase.ByItsArms(arms);
    }

    /**
     * What {@code value} answers where it is a call of a behavior that is no dependency the row
     * stands in: the case its body answers, read where the call stands with the parameters standing
     * for what the call handed ({@link #intoACall}) — or null where it is no such call.
     *
     * @param nowhere what the value is, as the place it stands at no position, where what the body
     *                answers is made of nothing followed back to the input
     */
    private WhichCase calledFor(Denotation value,
                                               WhyUnread.AtNoPosition.Place nowhere) {
        Denotation stands = value.at().standing(value.value(), read.rules().symbols(),
                read.rules().newtypes());
        if (!(AnOperationApplied.of(Core.withoutStanding(stands.value()))
                instanceof AnOperationApplied(ValueName.Behavior behavior, List<Core> _))
                || stands.at().standsIn(behavior)) {
            return null;
        }
        Inside.ACall called = intoACall(stands);
        return called == null
                ? new WhichCase.Unread(whatABehaviorAnswers(behavior, stands.at()))
                : throughTheBody(behavior, answered(called.body(), nowhere));
    }

    /** {@code answered}, read off the body of {@code behavior} where a call stands, with each arm
     *  reached as the body reaches it ({@link Derivation.ABehaviorsBody}). */
    private static WhichCase throughTheBody(ValueName.Behavior behavior,
                                                           WhichCase answered) {
        return switch (answered) {
            case WhichCase.Written _, WhichCase.Unread _,
                 WhichCase.AtAnInput _, WhichCase.AtAnAnswer _ ->
                    answered;
            case WhichCase.ByItsArms(var arms) ->
                    new WhichCase.ByItsArms(arms.stream().map(arm ->
                            new WhichCase.Arm(
                                    new Derivation.ABehaviorsBody(behavior, arm.reached()),
                                    throughTheBody(behavior, arm.answers()))).toList());
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
                    new WhyUnread.NoWordsFor(operation, OperationLaw.Observed.of(aspect), why),
                    fixed(e, reads)), stopsAt);
            case BoundOperationFacts.Settled.Open _ -> leaf(new Derivation.Stopped(
                    new WhyUnread.NotProvedOfItsBody(operation, OperationLaw.Observed.of(aspect)),
                    fixed(e, reads)), stopsAt);
            case BoundOperationFacts.Settled.ByALaw(
                    OperationLaw.Observation<DeclaredArgument> law, var _) ->
                    new Derivation.ByALaw(callOf(operation, applied, reads,
                            LawArguments.named(law.equivalentTo())), aspect,
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

    /** What each number of a law's form was read as at a call, or why one was not. */
    private sealed interface Numbers {

        record EachNumber(Map<LawNumber<?>, LinearForm<Quantity>> each) implements Numbers {}

        record NotRead(WhyUnread why) implements Numbers {}
    }

    /** What an element a law names is, inside a statement about some element of its container. */
    private sealed interface ElementAt {

        /** The element of the container {@code container} is: one a row writes, or one inside what
         *  a dependency answered. */
        record AtASubject(DecisionSubject container) implements ElementAt {}

        /**
         * A value the element is, read in {@code at}: one the source wrote out, or what a walk
         * answered on one element of what it walked.
         */
        record AValue(Core value, InputReads at) implements ElementAt {}

        /** One of the pieces of a string a split leaves, or one of its characters, whichever one
         *  the statement is about. */
        record APiece(Pieces of) implements ElementAt {}

        /**
         * An entry of a map a fold built by filing a counter under the key of each element of a
         * list ({@link KeyedAccumulation}): whichever element's key the entry is for. It is no
         * value of the input and stands at no position, so what a statement about it is about is
         * how often its key occurs.
         */
        record AnEntry() implements ElementAt {}

        /**
         * Any element of what {@code operation} answered, of which nothing is known but the side
         * every element of that answer comes out on ({@link Derivation.EveryElementMeetsIt}). It
         * stands at no position, and is no value written out.
         */
        record OfAnAnswerEveryElementOfWhichIs(ValueName operation, SideAnswered side)
                implements ElementAt {}

        /**
         * An entry of a map filed from the list at {@code list}: the list's own element, under the
         * key {@code key} makes of it. Of two elements of one key the later is the entry, so what
         * a statement is about is the last element of its key.
         */
        record AFiledElement(TermPath list, Core.Block key) implements ElementAt {

            public AFiledElement {
                Objects.requireNonNull(list, "an entry is an element of some list");
                Objects.requireNonNull(key, "an element is filed under what some closure makes");
            }
        }
    }

    /**
     * What a container is made of beneath the operations that kept or reordered its elements:
     * what they were handed, and what each kept them by, read where that operation was called.
     */
    private record Beneath(Denotation at, List<Kept> kept) {}

    /**
     * An operation that kept the elements meeting a statement, how that is read, and what an
     * element is at the level of the container its closure is handed: what stands at a position,
     * or the answer a walk gave, which a closure is handed where nothing else stands for it.
     */
    private record Kept(ALawRead read, LawNumber.HowManyMeet<DeclaredArgument> meeting,
                        ElementAt each, Denotation handed) {}

    /** Where a container's elements stand, what each is there for the statement quantified over
     *  them, and what was kept of them on the way — and, where they are the pieces of a string
     *  rather than something standing at a position, which pieces. What stands there is held only
     *  for a value a dependency answered, whose type nothing else says; a position of the input has
     *  its type from the declarations, which is asked where it is wanted. */
    private record Located(DecisionSubject held, Type heldType, ElementAt each,
                           Denotation handed, List<Kept> kept, Pieces pieces) {}

    /** One walk a container is the answer of: the step's answer on one element of what it walks,
     *  read where the walk is, the name the step gives that element, what it walks, and whether
     *  the container holds what a closure made of every element rather than one value for each. */
    private record AStep(Denotation answer, Core.Binder element, Denotation walked,
                         boolean holdsTheAnswers) {}

    /** The pieces of the string at {@code string} that a split at {@code separator}, one code
     *  point, leaves — or, with no separator, its characters, each code point a piece. */
    private record Pieces(TermPath string, OptionalInt separator) {}

    /** A statement read of each value a container written out holds, or why it was not. */
    private sealed interface WrittenOutRead {

        record Each(List<Derivation> each) implements WrittenOutRead {}

        record Stops(WhyUnread why) implements WrittenOutRead {}
    }

    private Sized sizeOf(Core value, InputReads at) {
        // Where it stands once the names and the arms taken are followed.
        Denotation made = at.standing(value, read.rules().symbols(), read.rules().newtypes());
        if (made.at().pathOf(made.value(), read.rules().newtypes())
                instanceof PathResolution.At(TermPath held)) {
            NumericTerm.TakenOf size = sizeAt(held);
            return size == null ? new Sized.NotSized(new WhyUnread.NoMeasureOfItsSize())
                    : new Sized.AsAForm(LinearForm.atom(new DecisionAtom.OfTheInput(size)));
        }
        // What a dependency answered holds as many as the library counts of it.
        DecisionSubject.AnAnswer answered = answerAt(made.value(), made.at());
        if (answered != null) {
            DecisionAtom size = sizeOfSubject(answered, made.value().type());
            return size == null ? new Sized.NotSized(new WhyUnread.NoMeasureOfItsSize())
                    : new Sized.AsAForm(LinearForm.atom(size));
        }
        // A list written out holds as many as it was written with.
        if (Core.withoutStanding(made.value()) instanceof Core.ListLit written) {
            return new Sized.AsAForm(LinearForm.constant(ExactRatio.of(written.elements().size())));
        }
        if (!(AnOperationApplied.of(Core.withoutStanding(made.value()))
                instanceof AnOperationApplied applied
                && applied.operation() instanceof ValueName.Stdlib operation)) {
            return new Sized.NotSized(
                    new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT));
        }
        Core e = Core.withoutStanding(made.value());
        // In the case of its size the comparison is being read in, the number that case says.
        LinearForm<Quantity> inACase = sizedInACase.get(e);
        if (inACase != null) {
            return new Sized.AsAForm(inACase);
        }
        return switch (DefaultBoundOperationFacts.get().settled(operation,
                OperationLaw.Observed.SIZE)) {
            case null -> {
                ValueName.Stdlib measure = NumericMeasures.takenOf(value.type(),
                        read.rules().inners());
                yield new Sized.NotSized(measure == null
                        ? new WhyUnread.NoMeasureOfItsSize()
                        : new WhyUnread.ANumberOfWhatAnOperationAnswers(measure, operation));
            }
            case BoundOperationFacts.Settled.Unsaid(Unsayable why) -> new Sized.NotSized(
                    new WhyUnread.NoWordsFor(operation, OperationLaw.Observed.SIZE, why));
            case BoundOperationFacts.Settled.Open _ -> new Sized.NotSized(
                    new WhyUnread.NotProvedOfItsBody(operation, OperationLaw.Observed.SIZE));
            case BoundOperationFacts.Settled.ByALaw(
                    OperationLaw.Size<DeclaredArgument> law, var _) -> {
                LinearForm<LawNumber<DeclaredArgument>> equalTo = law.unconditional();
                // Which number it is turns on how the arguments stand: a comparison over it is
                // read in each of its cases ({@link #inEachCaseOf}), and anywhere else it is no
                // one number, and stands at no position either.
                yield equalTo == null ? new Sized.NotSized(
                        new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT))
                        : new ALawRead(applied, e, made.at()).number(equalTo);
            }
            case BoundOperationFacts.Settled.ByALaw(
                    OperationLaw.Observation<DeclaredArgument> _, var _) ->
                    throw new IllegalStateException(operation + " settles how many it holds with"
                            + " a side of its answer");
        };
    }

    /**
     * The law sizing what {@code value} answers by cases, with the call — or null where it is no
     * call of an operation whose size turns on how its arguments stand.
     */
    private SizedByCases sizedByCases(Core value, InputReads at) {
        Denotation made = at.standing(value, read.rules().symbols(), read.rules().newtypes());
        Core e = Core.withoutStanding(made.value());
        return AnOperationApplied.of(e) instanceof AnOperationApplied applied
                && applied.operation() instanceof ValueName.Stdlib operation
                && DefaultBoundOperationFacts.get().settled(operation, OperationLaw.Observed.SIZE)
                        instanceof BoundOperationFacts.Settled.ByALaw(
                                OperationLaw.Size<DeclaredArgument> law, var _)
                && law.unconditional() == null
                ? new SizedByCases(applied, operation, e, made.at(), law) : null;
    }

    /** A call of {@code operation}, at {@code e} where it stands in {@code reads}, sized by the
     *  cases of {@code law}. */
    private record SizedByCases(AnOperationApplied applied, ValueName.Stdlib operation, Core e,
                                InputReads reads, OperationLaw.Size<DeclaredArgument> law) {}

    /**
     * A call sized by cases whose size {@code value} takes somewhere inside it, and not in a case
     * already: the innermost, so that what an outer one's cases say of it is read in one of its
     * own — or null where it takes none.
     */
    private SizedByCases measuredByCases(Denotation value) {
        return measuredByCases(value, new IdentityHashMap<>());
    }

    /**
     * The same, walking each value once however many names stand for it: {@code walked} holds
     * each value this search has walked already, with each reading it was walked in.
     *
     * <p>The value by identity and the reading by what it holds. A name stands for the very node
     * its binding was given, so one value reached by two names is one node; the reading round it
     * is made again each time a name is followed, and two of those that hold the same are one
     * place to have been. Told by the node's contents, every visit hashed the tree under it; told
     * by the reading's identity, a chain of names each using the one before it twice was walked
     * once for every way down it.
     */
    private SizedByCases measuredByCases(Denotation value,
                                         Map<Core, Set<InputReads>> walked) {
        Denotation stands = value.at().standing(value.value(), read.rules().symbols(),
                read.rules().newtypes());
        Core e = Core.withoutStanding(stands.value());
        // A closure's body is read where it is applied, and is no part of this value.
        if (e instanceof Core.Block || !walked.computeIfAbsent(stands.value(),
                _ -> new HashSet<>()).add(stands.at())) {
            return null;
        }
        SizedByCases[] inner = {null};
        Core.forEachChild(e, child -> {
            if (inner[0] == null) {
                inner[0] = measuredByCases(new Denotation(child, stands.at()), walked);
            }
        });
        if (inner[0] != null) {
            return inner[0];
        }
        if (AnOperationApplied.of(e) instanceof AnOperationApplied measuring
                && measuring.operation() instanceof ValueName.Stdlib measure
                && DefaultBoundOperationFacts.get().takenAs(measure)
                        instanceof TakenAs.HowManyItHolds
                && measuring.args().size() == 1) {
            SizedByCases sized = sizedByCases(measuring.args().getFirst(), stands.at());
            return sized != null && !sizedInACase.containsKey(sized.e()) ? sized : null;
        }
        return null;
    }

    /**
     * What {@code read} comes to in each case of how many {@code sized} answers: the arguments
     * standing as that case says, and {@code read} again with that many standing for the size.
     */
    private Derivation inEachCaseOf(SizedByCases sized, Denotation at,
                                    Supplier<Derivation> read) {
        ALawRead law = new ALawRead(sized.applied(), sized.e(), sized.reads());
        List<Derivation.MatchArms.Arm> arms = new ArrayList<>();
        for (OperationLaw.Size.Case<DeclaredArgument> each : sized.law().cases()) {
            Derivation reached = law.of(each.where());
            Derivation there = switch (law.number(each.equalTo())) {
                case Sized.NotSized(WhyUnread why) ->
                        partOf(at, new Derivation.Stopped(why, false));
                case Sized.AsAForm(LinearForm<Quantity> form) -> {
                    sizedInACase.put(sized.e(), form);
                    try {
                        yield read.get();
                    } finally {
                        sizedInACase.remove(sized.e());
                    }
                }
            };
            arms.add(new Derivation.MatchArms.Arm(reached, there));
        }
        Set<DeclaredArgument> named = new HashSet<>();
        sized.law().cases().forEach(each -> named.addAll(LawArguments.named(each.where())));
        return new Derivation.ASizeInCases(
                callOf(sized.operation(), sized.applied(), sized.reads(), named), arms);
    }

    /**
     * {@code applied}, a call of {@code operation} read in {@code reads}, with where each of the
     * arguments {@code named} stands: at the position of the input it is, for those that are one.
     */
    private Derivation.TheCall callOf(ValueName.Stdlib operation, AnOperationApplied applied,
                                      InputReads reads, Set<DeclaredArgument> named) {
        Map<DeclaredArgument, TermPath> standingAt = new HashMap<>();
        for (DeclaredArgument each : named) {
            Core argument = applied.argument(each);
            if (argument != null && reads.pathOf(argument, read.rules().newtypes())
                    instanceof PathResolution.At(TermPath at)) {
                standingAt.put(each, at);
            }
        }
        return new Derivation.TheCall(operation, standingAt);
    }

    /** The number a size of the container at {@code held} is, or null where no type measures it. */
    private NumericTerm.TakenOf sizeAt(TermPath held) {
        Type container = read.domain().typeAt(held, read.rules());
        ValueName.Stdlib size = container == null ? null
                : NumericMeasures.takenOf(container, read.rules().inners());
        return size == null ? null : NumericTerm.TakenOf.asItStands(size, held, container,
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

        /** {@code read}, part way through, carried on in {@code reads}. */
        private ALawRead(ALawRead read, InputReads reads) {
            this(read.applied, read.e, reads);
            this.elements.putAll(read.elements);
            this.application = read.application;
        }

        /**
         * {@code law} read at the call: each part of it as the step that reads that part, with
         * what the arguments are read as — and what each part comes to is that step's to work
         * out ({@link Derivation.ALawPart}).
         */
        Derivation of(LawProposition<DeclaredArgument> law) {
            return switch (law) {
                case LawProposition.Always<DeclaredArgument> always ->
                        new Derivation.ALawSettles(always);
                case LawProposition.All<DeclaredArgument> all ->
                        new Derivation.ALawJoins(all, all.parts().stream().map(this::of).toList());
                case LawProposition.Any<DeclaredArgument> any -> {
                    List<Disjunct.ImpliesAnother> implies = new ArrayList<>();
                    for (LawProposition<DeclaredArgument> part : any.parts()) {
                        implies.add(anotherItImplies(any, part));
                    }
                    if (implies.stream().allMatch(Objects::isNull)) {
                        yield new Derivation.ALawJoins(any,
                                any.parts().stream().map(this::of).toList());
                    }
                    List<Disjunct> each = new ArrayList<>();
                    for (int i = 0; i < implies.size(); i++) {
                        each.add(implies.get(i) != null ? implies.get(i)
                                : new Disjunct.Read(of(any.parts().get(i))));
                    }
                    yield new Derivation.ALawJoinsWithoutWhatImpliesAnother(any, each);
                }
                case LawProposition.Observed<DeclaredArgument> observed ->
                        new Derivation.OnTheSideALawNames(observed,
                                observed(observed.of(), observed.side().aspect()));
                case LawProposition.Compared<DeclaredArgument> compared -> compared(compared);
                case LawProposition.SomeElement<DeclaredArgument> some ->
                        new Derivation.ALawQuantifies(some, observe(
                                applied.argument(some.container()),
                                new Asked.SomeElement(this, some), reads));
                case LawProposition.Same<DeclaredArgument> same -> {
                    DecisionSubject one = subject(same.one());
                    DecisionSubject other = subject(same.other());
                    yield one == null || other == null
                            ? unread(e, reads,
                                    new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.VALUE))
                            : leaf(new Derivation.TheSameValue(same, one, other), e, reads);
                }
            };
        }

        /**
         * The part of {@code any} that {@code part} implies at this call, where there is one
         * ({@link Derivation.ALawJoinsWithoutWhatImpliesAnother}) — or null where it implies none.
         */
        private Disjunct.ImpliesAnother anotherItImplies(LawProposition.Any<DeclaredArgument> any,
                                                         LawProposition<DeclaredArgument> part) {
            for (LawProposition<DeclaredArgument> other : any.parts()) {
                if (other instanceof LawProposition.SomeElement<DeclaredArgument> some
                        && some.holds() && Derivation.ALawJoinsWithoutWhatImpliesAnother
                                .holdsOnlyWhereItHoldsSomething(part, some.container())) {
                    ValueName made = answeredBy(applied.argument(some.container()), reads);
                    if (made != null
                            && Derivation.EveryElementMeetsIt.askedOfEveryElement(some, made)) {
                        return new Disjunct.ImpliesAnother(some, made);
                    }
                }
            }
            return null;
        }

        /**
         * Some element of {@code made} meeting {@code some}, where what {@code some} asks of an
         * element comes out the same for every one of them ({@link Derivation.EveryElementMeetsIt})
         * — or null where what is asked turns on which element it is, or nothing says what an
         * element is.
         *
         * <p>What an element is, is read down through what {@code made} was made of, as
         * {@link #locate} reads it, to a container nothing below makes: through each walk that
         * answers one value for each element of what it walks, or what a closure made of every
         * element and no more, the element is the step's answer on one there; through each
         * operation that only reorders the elements or keeps some, it is one of them, together
         * with what it was kept by. Some element of {@code made} is there exactly where that
         * container holds something. Of the container's own element nothing is known but the
         * side every element of the operation that answered it comes out on, where it is such an
         * answer — no position of the input is asked for, since what is asked of the element
         * settles without one, or is asked of a value written without the element at all: what
         * the outermost closure answers, where it never reads the element it is handed, is one
         * value for every element, and what is stated of it is stated once.
         *
         * @param standing what {@code made} stands for, once the names it is are followed
         */
        private Derivation everyElementMeets(Denotation made, Denotation standing,
                                             LawProposition.SomeElement<DeclaredArgument> some) {
            List<Kept> located = new ArrayList<>();
            List<Kept> pending = new ArrayList<>();
            ElementAt outerEach = null;
            Denotation outerHanded = null;
            Derivation.EveryElementMeetsIt.Alike.WrittenWithoutTheElement writtenWithout = null;
            Denotation at = standing;
            boolean peeled = false;
            while (true) {
                Beneath below = beneath(at, false);
                if (below != null) {
                    pending.addAll(below.kept());
                    at = below.at();
                    peeled = true;
                }
                AStep walk = stepBeneath(at, false);
                if (walk == null) {
                    break;
                }
                Denotation step = walk.answer();
                ElementAt each = new ElementAt.AValue(step.value(), step.at());
                Denotation handed = walk.holdsTheAnswers() ? step : null;
                settle(pending, each, handed, located);
                if (outerEach == null) {
                    outerEach = each;
                    outerHanded = handed;
                    BindingId element = walk.element().binding();
                    writtenWithout = element == null ? null
                            : WhatABodyReads.without(step.value(), element).map(
                                    Derivation.EveryElementMeetsIt.Alike
                                            .WrittenWithoutTheElement::new).orElse(null);
                }
                at = walk.walked();
                peeled = true;
            }
            AnOperationApplied answering = AnOperationApplied.of(at.value());
            ValueName operation = answering == null ? null : answering.operation();
            SideAnswered side = operation == null ? null
                    : DefaultBoundOperationFacts.get().everyElementOfItsAnswerIs(operation);
            ElementAt beneathAll = side == null ? null
                    : new ElementAt.OfAnAnswerEveryElementOfWhichIs(operation, side);
            if (beneathAll == null && (outerEach == null || !pending.isEmpty())) {
                return null;
            }
            settle(pending, beneathAll, null, located);
            Derivation ofTheElement;
            if (outerHanded != null) {
                ofTheElement = ofTheValue(some.container(), some.ofTheElement(), outerHanded);
            } else {
                elements.put(some.container(), outerEach != null ? outerEach : beneathAll);
                try {
                    ofTheElement = of(some.ofTheElement());
                } finally {
                    elements.remove(some.container());
                }
            }
            ofTheElement = alsoWhatWasKept(ofTheElement, located);
            Derivation.EveryElementMeetsIt.Alike alike =
                    trying.of(ofTheElement) instanceof Proposition.Always
                            ? new Derivation.EveryElementMeetsIt.Alike.Settled()
                            : writtenWithout != null && Derivation.EveryElementMeetsIt
                                    .keptOnlyByWhatSettlesTrue(ofTheElement)
                                    ? writtenWithout : null;
            if (alike == null) {
                return null;
            }
            Denotation holding = peeled ? at : made;
            return new Derivation.EveryElementMeetsIt(some, ofTheElement,
                    observe(holding.value(), AnswerAspect.EMPTINESS, holding.at()), alike);
        }

        /** The operation whose answer {@code given} stands for, read in {@code at}, or null where
         *  it stands for no operation's answer. */
        private ValueName answeredBy(Core given, InputReads at) {
            AnOperationApplied made = AnOperationApplied.of(
                    at.standing(given, read.rules().symbols(), read.rules().newtypes()).value());
            return made == null ? null : made.operation();
        }

        /** How {@code subject} coming out on {@code aspect}'s holding side was read. */
        private Derivation observed(LawSubject<DeclaredArgument> subject, AnswerAspect aspect) {
            return switch (subject) {
                case LawSubject.Argument<DeclaredArgument>(DeclaredArgument at) ->
                        observe(applied.argument(at), aspect, reads);
                case LawSubject.ElementOf<DeclaredArgument>(DeclaredArgument at) ->
                        switch (elements.get(at)) {
                            // A value the element is is read as itself, where it was given.
                            case ElementAt.AValue(Core value, InputReads in) ->
                                    observe(value, aspect, in);
                            case ElementAt.AtASubject(DecisionSubject container) ->
                                    observedAt(container.element(), aspect);
                            case ElementAt.AFiledElement(TermPath list, Core.Block _) ->
                                    observedAt(new DecisionSubject.AnInput(list.element()),
                                            aspect);
                            // Of an element known only by the side every element of an answer
                            // comes out on, that side is known and no other.
                            case ElementAt.OfAnAnswerEveryElementOfWhichIs(var operation,
                                                                          var side) ->
                                    side.aspect() == aspect
                                            ? new Derivation.OfAnElementOfAnAnswer(operation,
                                                    side)
                                            : unread(e, reads, new WhyUnread.AtNoPosition(
                                                    WhyUnread.AtNoPosition.Place.SUBJECT));
                            // A piece, and an entry filed by a fold, stand at no position of the
                            // input to be observed there.
                            case ElementAt.APiece _, ElementAt.AnEntry _ -> unread(e, reads,
                                    new WhyUnread.AtNoPosition(
                                            WhyUnread.AtNoPosition.Place.SUBJECT));
                        };
                case LawSubject.WhatTheClosureAnswers<DeclaredArgument>(DeclaredArgument at) -> {
                    Denotation answered = whatTheClosureAnswers(at);
                    yield answered != null ? observe(answered.value(), aspect, answered.at())
                            : unread(e, reads, aClosureNotMet());
                }
                case LawSubject.KeyOf<DeclaredArgument>(DeclaredArgument at) -> {
                    DecisionSubject key = keyAt(at);
                    yield key != null ? observedAt(key, aspect) : unread(e, reads,
                            new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT));
                }
                case LawSubject.AnswerOf<DeclaredArgument> _ -> throw namedInNoLaw(subject);
            };
        }

        /** The value standing at {@code at} coming out on {@code aspect}'s holding side. */
        private Derivation observedAt(DecisionSubject at, AnswerAspect aspect) {
            return switch (aspect) {
                case TRUTH -> leaf(new Derivation.ATruthOfASubject(at, true), e, reads);
                case PRESENCE -> leaf(new Derivation.PresentInASubject(at), e, reads);
                case EMPTINESS -> {
                    Derivation some = holdsSomethingAt(at, null);
                    yield leaf(some != null ? some : new Derivation.Stopped(
                            new WhyUnread.NoMeasureOfItsSize(), false), e, reads);
                }
            };
        }

        /**
         * What the closure handed as the argument {@code at} answers: its body, read where one
         * application of it is, or where the closure stands where no application is being read —
         * or null where it stands for no block whose body the reading can read.
         */
        private Denotation whatTheClosureAnswers(DeclaredArgument at) {
            Denotation closure = reads.denotes(applied.argument(at), read.rules().symbols(),
                    read.rules().newtypes());
            return Core.withoutStanding(closure.value()) instanceof Core.Block block
                    ? new Denotation(block.body(),
                            application != null ? application : closure.at())
                    : null;
        }

        /**
         * The position the key the element of the map at {@code at} is filed under stands at, or
         * null where the element is a value written out rather than one standing at a position —
         * a value is handed on without the key it was filed under.
         */
        private DecisionSubject keyAt(DeclaredArgument at) {
            return switch (elements.get(at)) {
                case ElementAt.AtASubject(DecisionSubject map) -> map.key();
                // The entry under a key is an element of the list, so the key it stands under is
                // what the closure makes of that element.
                case ElementAt.AFiledElement(TermPath list, Core.Block key) -> {
                    TermPath filed =
                            reads.keyOfTheElement(key, list.element(), read.rules().newtypes());
                    yield filed == null ? null : new DecisionSubject.AnInput(filed);
                }
                case ElementAt.AValue _, ElementAt.APiece _, ElementAt.AnEntry _,
                     ElementAt.OfAnAnswerEveryElementOfWhichIs _ -> null;
                case null -> null;
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
                            case ElementAt.AtASubject(DecisionSubject container) ->
                                    container.element();
                            case ElementAt.AFiledElement(TermPath list, Core.Block _) ->
                                    new DecisionSubject.AnInput(list.element());
                            case ElementAt.AValue(Core value, InputReads in) ->
                                    in.pathOf(value, read.rules().newtypes())
                                            instanceof PathResolution.At(TermPath held)
                                            ? new DecisionSubject.AnInput(held)
                                            : answerAt(value, in);
                            case ElementAt.APiece _, ElementAt.AnEntry _,
                                 ElementAt.OfAnAnswerEveryElementOfWhichIs _ -> null;
                        };
                case LawSubject.WhatTheClosureAnswers<DeclaredArgument> _ -> null;
                case LawSubject.KeyOf<DeclaredArgument>(DeclaredArgument at) -> keyAt(at);
                case LawSubject.AnswerOf<DeclaredArgument> _ -> throw namedInNoLaw(subject);
            };
        }

        /**
         * Some element of {@code made}, a container no binding, name or choice made, meeting
         * {@code some} — by the first of the rules for it that reads all of it ({@link RuleChoice}).
         *
         * <p>Read on the reading that takes the argument the call was handed as {@code made}
         * ({@link InputReads#taking}): where the argument is chosen by cases or answered by a body,
         * {@code made} is what it is on the case this is read on, and the elements the closure is
         * handed are that container's.
         */
        Derivation someElementOf(Denotation made,
                                 LawProposition.SomeElement<DeclaredArgument> some) {
            Core argument = applied.argument(some.container());
            // A node taken as itself is taken as nothing.
            ALawRead on = Core.withoutStanding(made.value()) == Core.withoutStanding(argument)
                    ? this : new ALawRead(this, reads.taking(argument, made, 1));
            Denotation container = made.at().standing(made.value(), read.rules().symbols(),
                    read.rules().newtypes());
            return firstThatReadsIt(List.of(
                    () -> on.meeting(made, container, some),
                    () -> on.everyElementMeets(made, container, some),
                    () -> inTheCalledBody(made.value(), new Asked.SomeElement(this, some),
                            made.at())));
        }

        /**
         * Some element of a container meeting a statement, read as the quantifier over the
         * container's element where it stands, or element by element where it was written out.
         *
         * @param standing what {@code made} stands for, once the names it is are followed
         */
        private Derivation meeting(Denotation made, Denotation standing,
                                   LawProposition.SomeElement<DeclaredArgument> some) {
            Core given = made.value();
            // A container the source wrote out has some element meeting a statement where one of
            // the occurrences it holds does and is kept; and so does a list an operation put
            // together of pieces of one, each occurrence kept where what made it says.
            WrittenOutElements.Walked whole = eachValue(standing);
            if (whole instanceof WrittenOutElements.Walked.Each each) {
                return someOf(some, there(each));
            }
            if (whole instanceof WrittenOutElements.Walked.PastTheFigure) {
                return unread(e, reads, new WhyUnread.MoreReadingsThanAreMade());
            }
            Denotation container = standing;
            // Another order of the same elements has some element meeting a statement where they
            // do, and what an operation kept of them has one where some element it was handed
            // meets that and what it kept by.
            Beneath beneath = beneath(container, false);
            Core over = beneath == null ? given : beneath.at().value();
            InputReads in = beneath == null ? made.at() : beneath.at().at();
            List<Kept> kept = beneath == null ? List.of() : beneath.kept();
            if (beneath != null) {
                container = beneath.at();
            }
            WrittenOutElements.Walked values = beneath == null ? whole : eachValue(container);
            if (values instanceof WrittenOutElements.Walked.PastTheFigure) {
                return unread(e, reads, new WhyUnread.MoreReadingsThanAreMade());
            }
            // An element that is a given value and also met what it was kept by is one a row cannot
            // be asked for: the value is written into the container as an element of its own.
            if (!kept.isEmpty() && (values instanceof WrittenOutElements.Walked.Each
                    || statesTheValueOfTheElement(some.ofTheElement()))) {
                return unread(over, in,
                        new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.CONTAINER));
            }
            if (values instanceof WrittenOutElements.Walked.Each each) {
                return someOf(some, there(each));
            }
            // A container at a position has the element standing there; a walk's answer over one
            // has, for each element there, the step's answer on it.
            Located located = locate(container, over, in, kept, false);
            if (located == null) {
                return unread(over, in,
                        new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.CONTAINER));
            }
            DecisionSubject heldAt = located.held();
            Derivation answered = located.handed() == null
                    ? aboutAnElement(some.container(), heldAt, located.each(),
                            some.ofTheElement())
                    : aboutTheValue(some.container(), heldAt, some.ofTheElement(),
                            located.handed());
            if (answered == null) {
                return unread(e, reads, new WhyUnread.TwoElementsOfOneContainer());
            }
            // The entry a map holds under a key is the last element the key was made of, so what
            // is stated of an entry is stated of the last element of its key.
            if (located.each() instanceof ElementAt.AFiledElement(TermPath list, Core.Block key)) {
                TermPath filedUnder = reads.keyOfTheElement(key, list.element(),
                        read.rules().newtypes());
                if (filedUnder == null) {
                    return unread(e, reads, new WhyUnread.AtNoPosition(
                            WhyUnread.AtNoPosition.Place.SUBJECT));
                }
                answered = leaf(new Derivation.OfTheLastToHoldItsValue(answered, list, filedUnder),
                        e, reads);
            }
            answered = alsoWhatWasKept(answered, located.kept());
            Proposition element = trying.of(answered);
            if (located.pieces() != null) {
                return somePiece(located.pieces(), answered, element, over, in);
            }
            Optional<Derivation> holdsSomething = Optional.empty();
            if (Derivation.SomeElementMeeting.asksWhetherItHoldsAnything(heldAt, element)) {
                DecisionAtom size = sizeOfSubject(heldAt, located.heldType());
                holdsSomething = Optional.of(size != null
                        ? leaf(new Derivation.SizeAboveNought(size),
                                askedAt != null ? askedAt : new Denotation(e, reads))
                        : unread(over, in, new WhyUnread.NoMeasureOfItsSize()));
            }
            return new Derivation.SomeElementMeeting(heldAt, answered, true, holdsSomething);
        }

        /**
         * Some piece of the string meeting {@code element}, which is what was read of one piece:
         * the string holding a code point the pieces meeting it hold ({@link
         * Derivation.SomePieceMeeting}) — where that is all that was asked of the piece.
         *
         * <p>What else may be asked of a piece split at a separator is not what the string holds.
         * That it holds none, or how many, or that it is as long as something, turns on how the
         * separator stands in the string, and nothing of the input says that: it stops there. Of
         * a character, every code point the set holds, the string holding one is the string
         * holding anything, which is how long it is.
         */
        private Derivation somePiece(Pieces pieces, Derivation answered, Proposition element,
                                     Core over, InputReads in) {
            CodePoints held = Derivation.SomePieceMeeting.held(pieces.separator(), element);
            if (held == null) {
                WhyUnread stopped = Proposition.firstStopIn(element);
                return unread(over, in, stopped != null ? stopped : new WhyUnread.AtNoPosition(
                        WhyUnread.AtNoPosition.Place.CONTAINER));
            }
            NumericTerm counted = null;
            if (!held.isEmpty()) {
                Type type = read.domain().typeAt(pieces.string(), read.rules());
                counted = held.isEverything() ? sizeAt(pieces.string()) : type == null ? null
                        : NumericTerm.CodePointClassCount.of(pieces.string(),
                                CodePointClass.of(held), type, read.rules().inners());
                if (counted == null) {
                    return unread(over, in, new WhyUnread.NoMeasureOfItsSize());
                }
            }
            // Met as a part of its own, as how many a container holds above nought is: it is a
            // statement about a number of the string, which is what a line is drawn on.
            return leaf(new Derivation.SomePieceMeeting(pieces.string(), pieces.separator(),
                    Optional.ofNullable(counted), answered),
                    askedAt != null ? askedAt : new Denotation(e, reads));
        }

        /**
         * {@code ofTheElement} read of {@code element}, the element of {@code container}, which is
         * held one for each element of the container at {@code held} — or null where that
         * container is already quantified over: the element is what stands at the container's
         * element, so the same container quantified inside itself would name two elements one
         * subject.
         */
        private Derivation aboutAnElement(DeclaredArgument container, DecisionSubject held,
                                          ElementAt element,
                                          LawProposition<DeclaredArgument> ofTheElement) {
            if (!quantifying.add(held)) {
                return null;
            }
            elements.put(container, element);
            try {
                return of(ofTheElement);
            } finally {
                elements.remove(container);
                quantifying.remove(held);
            }
        }

        /** As {@link #aboutAnElement}, of the element that is {@code value}
         *  ({@link #ofTheValue}). */
        private Derivation aboutTheValue(DeclaredArgument container, DecisionSubject held,
                                         LawProposition<DeclaredArgument> ofTheElement,
                                         Denotation value) {
            if (!quantifying.add(held)) {
                return null;
            }
            try {
                return ofTheValue(container, ofTheElement, value);
            } finally {
                quantifying.remove(held);
            }
        }

        /**
         * What {@code container} is made of, beneath every operation that only puts the elements
         * of what it was handed in another order or keeps the ones meeting a statement — or null
         * where it is not the answer of one.
         */
        private Beneath beneath(Denotation container, boolean counting) {
            List<Kept> kept = new ArrayList<>();
            Denotation at = container;
            boolean peeled = false;
            while (Core.withoutStanding(at.value()) instanceof Core.PreservedCall call) {
                ValueName operation = call.declared().operation();
                BuiltFrom<DeclaredArgument> built =
                        DefaultBoundOperationFacts.get().buildsItsResultFrom(operation);
                DeclaredArgument from = built == null ? null : built.permutesTheElementsOf();
                if (from == null && built != null) {
                    DeclaredArgument holds = built.holdsTheElementsOf();
                    LawNumber.HowManyMeet<DeclaredArgument> keeping =
                            holds == null ? null : keepsWhatMeets(operation, holds);
                    if (keeping != null) {
                        from = holds;
                        kept.add(new Kept(new ALawRead(
                                new AnOperationApplied(operation, call.args()), call, at.at()),
                                keeping, null, null));
                    }
                }
                // Whether some element meets a statement is the same of a container holding the
                // same values, however many times it holds each.
                if (from == null && !counting
                        && DefaultBoundOperationFacts.get().holdsTheImageOfEveryElement(operation)
                        instanceof ElementLineage.SameAs<DeclaredArgument> same) {
                    from = same.source().argument();
                }
                if (from == null) {
                    break;
                }
                at = at.at().standing(call.args().get(from.position()),
                        read.rules().symbols(), read.rules().newtypes());
                peeled = true;
            }
            return peeled ? new Beneath(at, kept) : null;
        }

        /**
         * The statement {@code operation}'s answer holds exactly the elements of {@code from}
         * meeting, as its size says: as many as meet it, and the elements its own — or null where
         * its size is any other number.
         */
        private static LawNumber.HowManyMeet<DeclaredArgument> keepsWhatMeets(
                ValueName operation, DeclaredArgument from) {
            if (!(DefaultBoundOperationFacts.get().settled(operation, OperationLaw.Observed.SIZE)
                    instanceof BoundOperationFacts.Settled.ByALaw(
                            OperationLaw.Size<DeclaredArgument> law, var _))) {
                return null;
            }
            LinearForm<LawNumber<DeclaredArgument>> size = law.unconditional();
            if (size == null || size.constant().signum() != 0 || size.coefs().size() != 1) {
                return null;
            }
            Map.Entry<LawNumber<DeclaredArgument>, ExactRatio> only =
                    size.coefs().entrySet().iterator().next();
            return ExactRatio.ONE.equals(only.getValue())
                    && only.getKey() instanceof LawNumber.HowManyMeet<DeclaredArgument> meet
                    && meet.container().equals(from) ? meet : null;
        }

        /**
         * {@code answered}, what is stated of an element, together with what each operation that
         * kept the element kept it by states of it: the element is one of those it kept.
         */
        private Derivation alsoWhatWasKept(Derivation answered, List<Kept> kept) {
            if (kept.isEmpty()) {
                return answered;
            }
            List<Derivation> by = new ArrayList<>();
            for (Kept one : kept) {
                if (one.handed() != null) {
                    by.add(one.read().ofTheValue(one.meeting().container(),
                            one.meeting().ofTheElement(), one.handed()));
                    continue;
                }
                one.read().elements.put(one.meeting().container(), one.each());
                try {
                    by.add(one.read().of(one.meeting().ofTheElement()));
                } finally {
                    one.read().elements.remove(one.meeting().container());
                }
            }
            return new Derivation.OfWhatWasKept(answered, by);
        }

        /**
         * Every element of {@code container}, where they can all be written out: the values a list
         * was written with, or the pieces an operation put together of each element of such a list
         * — each occurrence with what it was kept by ({@link WrittenOutElements}).
         */
        private WrittenOutElements.Walked eachValue(Denotation container) {
            return WrittenOutElements.of(container, read.rules().symbols(),
                    read.rules().newtypes());
        }

        /** Some one of {@code occurrences} meeting what {@code some} says, each read where it is
         *  kept. */
        private Derivation someOf(LawProposition.SomeElement<DeclaredArgument> some,
                                  List<ReadMeaning.Occurrence> occurrences) {
            return switch (ofEachWrittenOut(some.container(), occurrences, some.ofTheElement())) {
                case WrittenOutRead.Each(List<Derivation> each) ->
                        new Derivation.OverElementsWrittenOut(each, true);
                case WrittenOutRead.Stops(WhyUnread why) -> unread(e, reads, why);
            };
        }

        /**
         * The occurrences {@code each} holds on some row, each with the truths it is still kept by
         * ({@link KeptTruths}): one dropped on every row is no element, and nothing stated of it is
         * part of a statement about some element or of a count of them.
         */
        private List<ReadMeaning.Occurrence> there(WrittenOutElements.Walked.Each each) {
            return each.occurrencesWhere(KeptTruths.readIn(read));
        }

        /**
         * {@code stated} of an occurrence, together with what it was kept by: an occurrence is one
         * of the container's elements where each truth it was kept by came out as it did, and a
         * statement about some element is about one that is there.
         */
        private Derivation whereItIsKept(Derivation stated,
                                         List<ReadMeaning.Occurrence.Kept> keptWhere) {
            if (keptWhere.isEmpty()) {
                return stated;
            }
            List<Derivation> by = new ArrayList<>();
            for (ReadMeaning.Occurrence.Kept kept : keptWhere) {
                Derivation truth = observe(kept.truth().value(), AnswerAspect.TRUTH,
                        kept.truth().at());
                by.add(kept.holds() ? truth : new Derivation.UnderADenial(truth, true));
            }
            return new Derivation.OfWhatWasKept(stated, by);
        }

        /**
         * The position the elements of {@code container} stand at, and what each is there — or null
         * where they stand at none. Through every walk that answers one value for each element of
         * what it walks, each element is the step's answer on one there; and, where only whether
         * some element meets a statement is asked, through the walks that answer what a closure
         * made of every element and no more, as a set made of them does, each element is the step's
         * answer on some one there. Beneath each walk what was kept of the elements is read of the
         * elements the level it is at has.
         *
         * @param container where the container is standing, with what it is made of beneath the
         *                  operations that kept or reordered its elements read off already
         * @param kept      what those operations kept their elements by
         * @param counting  whether how many elements meet a statement is asked, which a set made
         *                  of what a closure answered does not say
         */
        private Located locate(Denotation container, Core over, InputReads in, List<Kept> kept,
                               boolean counting) {
            List<Kept> located = new ArrayList<>();
            List<Kept> pending = new ArrayList<>(kept);
            ElementAt outerEach = null;
            Denotation outerHanded = null;
            Denotation at = container;
            Core value = over;
            InputReads where = in;
            while (true) {
                DecisionSubject standing = subjectOf(value, where);                if (standing != null) {
                    ElementAt each = new ElementAt.AtASubject(standing);
                    settle(pending, each, null, located);
                    Type heldType = Core.withoutStanding(value).type();
                    return outerEach == null
                            ? new Located(standing, heldType, each, null, located, null)
                            : new Located(standing, heldType, outerEach, outerHanded, located,
                                    null);
                }
                // The pieces of a string at a position, each of which is one of the elements and
                // no place a row writes. Only whether some piece meets a statement is asked of
                // them: how many of the pieces do depends on how the separator stands in the
                // string, which no number of the input says.
                Pieces pieces = counting ? null : piecesOf(at);
                if (pieces != null) {
                    ElementAt each = new ElementAt.APiece(pieces);
                    settle(pending, each, null, located);
                    DecisionSubject string = new DecisionSubject.AnInput(pieces.string());
                    return outerEach == null
                            ? new Located(string, null, each, null, located, pieces)
                            : new Located(string, null, outerEach, outerHanded, located, pieces);
                }
                AStep walk = stepBeneath(at, counting);
                // A map filed under the key of each element of a list: an entry is there for
                // some element of the list, so some entry is some element's. How many entries
                // meet a statement is not how many elements do — two elements of one key are one
                // entry — so only whether some one does is asked of them.
                if (walk == null && !counting) {
                    Located entries = entriesOf(at, pending, located, outerEach, outerHanded);
                    if (entries != null) {
                        return entries;
                    }
                    // A map holding the elements of a list under their keys: an entry is one of
                    // the list's elements, the last of its key.
                    Located filed = filedElementsOf(at, pending, located, outerEach, outerHanded);
                    if (filed != null) {
                        return filed;
                    }
                }
                if (walk == null) {
                    return null;
                }
                Denotation step = walk.answer();
                ElementAt each = new ElementAt.AValue(step.value(), step.at());
                Denotation handed = walk.holdsTheAnswers() ? step : null;
                settle(pending, each, handed, located);
                if (outerEach == null) {
                    outerEach = each;
                    outerHanded = handed;
                }
                at = walk.walked();
                Beneath below = beneath(at, counting);
                if (below != null) {
                    pending.addAll(below.kept());
                    at = below.at();
                }
                value = at.value();
                where = at.at();
            }
        }

        /**
         * The walk {@code container} is the answer of: one value for each element of what it
         * walks, or — where how many elements meet a statement is not asked — what a closure made
         * of every element and no more, which a set made of its answers holds. Or null where it is
         * the answer of no walk.
         */
        private AStep stepBeneath(Denotation container, boolean counting) {
            ElementBindings.StepOnEachElement walk = aWalk(container);
            boolean holdsTheAnswers = false;
            if (walk == null && !counting) {
                walk = ElementBindings.stepHoldingTheAnswerOnEachElement(container.value(),
                        blockIn(container));
                holdsTheAnswers = walk != null;
            }
            return walk == null ? null : new AStep(
                    new Denotation(walk.step().body(), container.at()), walk.element(),
                    container.at().standing(walk.walked(), read.rules().symbols(),
                            read.rules().newtypes()),
                    holdsTheAnswers);
        }

        /**
         * The pieces {@code container} is, where it is what an operation answering the pieces of a
         * string was given — a string at a position of the input, and a separator written as one
         * code point where it parts the string at one — or null where it is not.
         *
         * <p>A separator that is longer, or is not written out, is a call this does not say the
         * pieces of: a longer one can stand across where a shorter one is looked for, and one that
         * is not a constant is any of them.
         */
        private Pieces piecesOf(Denotation container) {
            if (!(Core.withoutStanding(container.value()) instanceof Core.PreservedCall call)) {
                return null;
            }
            BoundOperationFacts.Pieces parted =
                    DefaultBoundOperationFacts.get().piecesOf(call.declared().operation());
            if (parted == null) {
                return null;
            }
            OptionalInt separatedBy = OptionalInt.empty();
            if (parted.separator().isPresent()) {
                Denotation separator = container.at().standing(
                        call.args().get(parted.separator().get().position()),
                        read.rules().symbols(), read.rules().newtypes());
                if (!(Core.withoutStanding(separator.value()) instanceof Core.Str written)
                        || written.value().codePointCount(0, written.value().length()) != 1
                        || (written.value().length() == 1
                                && Character.isSurrogate(written.value().charAt(0)))) {
                    return null;
                }
                separatedBy = OptionalInt.of(written.value().codePointAt(0));
            }
            Denotation string = container.at().standing(
                    call.args().get(parted.string().position()), read.rules().symbols(),
                    read.rules().newtypes());
            return string.at().pathOf(string.value(), read.rules().newtypes())
                    instanceof PathResolution.At(TermPath at)
                    ? new Pieces(at, separatedBy) : null;
        }

        /**
         * The call, a pattern matched against one character of a string, as the character being
         * one of the code points the pattern accepts the string of alone ({@link
         * Derivation.ACharacterInAClass}) — or null where it is no such call: another predicate,
         * or a subject that is not a character.
         */
        Derivation aCharacterInAClass() {
            if (!(Core.withoutStanding(e) instanceof Core.PreservedCall call)
                    || !(call.settled() instanceof Core.KernelFact.StringMatches matches)
                    || !(call.operation() instanceof ValueName.Stdlib.Operation operation)) {
                return null;
            }
            StringPredicates predicate =
                    StringPredicates.of(read.rules().symbols().kernelOf(operation));
            Pieces piece = predicate == null ? null
                    : pieceThatIs(call.args().get(predicate.subject()), reads);
            return piece == null || piece.separator().isPresent() ? null
                    : leaf(new Derivation.ACharacterInAClass(matches.meaning()), e, reads);
        }

        /**
         * The pieces {@code e}, read in {@code at}, is one of — where it is a parameter a walk
         * hands each element of what an operation answering the pieces of a string was given, or
         * of what only kept some of those — or null where it is not.
         */
        private Pieces pieceThatIs(Core e, InputReads at) {
            Denotation standing = at.standing(e, read.rules().symbols(), read.rules().newtypes());
            Core container = standing.at().containerOfTheElement(standing.value());
            if (container == null) {
                return null;
            }
            Denotation whole = standing.at().standing(container, read.rules().symbols(),
                    read.rules().newtypes());
            Beneath beneath = beneath(whole, false);
            return piecesOf(beneath == null ? whole : beneath.at());
        }

        /**
         * Where the entries of {@code container} stand, where it is a map filed under the key of
         * each element of a list standing at a position — or null where it is not.
         */
        private Located entriesOf(Denotation container, List<Kept> pending, List<Kept> located,
                                 ElementAt outerEach, Denotation outerHanded) {
            KeyedAccumulation filed = KeyedAccumulation.of(container.value(), blockIn(container));
            if (filed == null) {
                return null;
            }
            Denotation walked = container.at().standing(filed.walked(), read.rules().symbols(),
                    read.rules().newtypes());
            if (!(walked.at().pathOf(walked.value(), read.rules().newtypes())
                    instanceof PathResolution.At(TermPath held))) {
                return null;
            }
            ElementAt each = new ElementAt.AnEntry();
            settle(pending, each, null, located);
            DecisionSubject heldAt = new DecisionSubject.AnInput(held);
            return outerEach == null ? new Located(heldAt, null, each, null, located, null)
                    : new Located(heldAt, null, outerEach, outerHanded, located, null);
        }

        /**
         * Where the entries of {@code container} stand, where it is a map holding each element of a
         * list standing at a position under the key a closure makes of it ({@link AnIndexedMap})
         * — or null where it is not. Only whether some entry meets a statement is asked of them:
         * how many do is not how many elements do, since of two elements of one key one is an
         * entry.
         */
        private Located filedElementsOf(Denotation container, List<Kept> pending,
                                        List<Kept> located, ElementAt outerEach,
                                        Denotation outerHanded) {
            AnIndexedMap indexed = AnIndexedMap.of(container.value(), blockIn(container));
            if (indexed == null) {
                return null;
            }
            Denotation walked = container.at().standing(indexed.walked(),
                    read.rules().symbols(), read.rules().newtypes());
            if (!(walked.at().pathOf(walked.value(), read.rules().newtypes())
                    instanceof PathResolution.At(TermPath held))) {
                return null;
            }
            ElementAt each = new ElementAt.AFiledElement(held, indexed.key());
            settle(pending, each, null, located);
            DecisionSubject heldAt = new DecisionSubject.AnInput(held);
            return outerEach == null ? new Located(heldAt, null, each, null, located, null)
                    : new Located(heldAt, null, outerEach, outerHanded, located, null);
        }

        /** What was kept at one level of a container, as the elements of that level are read. */
        private static void settle(List<Kept> pending, ElementAt each, Denotation handed,
                                   List<Kept> into) {
            pending.forEach(one -> into.add(new Kept(one.read(), one.meeting(), each, handed)));
            pending.clear();
        }

        /** The walk {@code container} is the answer of, one value for each element of what it
         *  walks, or null where it is none ({@link ElementBindings#stepAnsweredOnEachElement}). */
        private ElementBindings.StepOnEachElement aWalk(Denotation container) {
            return ElementBindings.stepAnsweredOnEachElement(container.value(),
                    blockIn(container));
        }

        /** The block a closure is, read where {@code container} stands. */
        private Function<Core, Core.Block> blockIn(Denotation container) {
            return blocksAt(container);
        }

        /**
         * {@code law} read of the element that is {@code value}, where the closure it names is
         * handed that value: what the closure answers is its answer on that application, and the
         * element is the value. For a container whose elements stand for no parameter of the
         * closure, which is every element of a set made of what a closure answered.
         */
        private Derivation ofTheValue(DeclaredArgument container,
                                      LawProposition<DeclaredArgument> law, Denotation value) {
            DeclaredArgument named = closureIn(law);
            elements.put(container, new ElementAt.AValue(value.value(), value.at()));
            InputReads outer = application;
            try {
                if (named != null) {
                    Denotation closure = reads.denotes(applied.argument(named),
                            read.rules().symbols(), read.rules().newtypes());
                    if (!(Core.withoutStanding(closure.value()) instanceof Core.Block block)) {
                        return unread(e, reads, aClosureNotMet());
                    }
                    InputReads handing = closure.at().handingTheElement(block,
                            applied.argument(container), value, read.rules().newtypes());
                    if (handing == null) {
                        return unread(e, reads, aClosureNotMet());
                    }
                    application = handing;
                }
                return of(law);
            } finally {
                elements.remove(container);
                application = outer;
            }
        }

        /**
         * {@code law} read of each of {@code occurrences}, the elements of the container
         * {@code container}: of the value itself where the law names the element, of what the
         * closure states on the application that hands it that value where the law names what the
         * closure answers, and of both together, on that application, where it names both — each
         * together with what its occurrence is still kept by.
         *
         * @param occurrences the ones there on some row ({@link #there})
         */
        private WrittenOutRead ofEachWrittenOut(DeclaredArgument container,
                                                List<ReadMeaning.Occurrence> occurrences,
                                                LawProposition<DeclaredArgument> law) {
            if (occurrences.isEmpty()) {
                return new WrittenOutRead.Each(List.of());
            }
            DeclaredArgument named = closureIn(law);
            List<Derivation> ofEach = new ArrayList<>();
            if (named == null) {
                if (occurrences.size() > READINGS.maximum()) {
                    return new WrittenOutRead.Stops(new WhyUnread.MoreReadingsThanAreMade());
                }
                for (ReadMeaning.Occurrence occurrence : occurrences) {
                    Denotation value = occurrence.value();
                    elements.put(container, new ElementAt.AValue(value.value(), value.at()));
                    try {
                        ofEach.add(whereItIsKept(of(law), occurrence.keptWhere()));
                    } finally {
                        elements.remove(container);
                    }
                }
                return new WrittenOutRead.Each(ofEach);
            }
            Denotation closure = reads.denotes(applied.argument(named), read.rules().symbols(),
                    read.rules().newtypes());
            if (!(Core.withoutStanding(closure.value()) instanceof Core.Block block)) {
                return new WrittenOutRead.Stops(aClosureNotMet());
            }
            if (namesTheElement(law, container)) {
                return onTheApplicationHandingEach(container, occurrences, closure, block, law);
            }
            // What the closure states on each application a run may make, where which it makes is
            // not said as much as where it is — each where the element it is handed is kept.
            List<InputReads.Applications.Made> applications = switch (applicationsOf(block,
                    closure.at(), read)) {
                case InputReads.Applications.Each(var each, var _) -> each;
                case InputReads.Applications.Unsaid(var each) -> each;
                case InputReads.Applications.NoneHanded _ ->
                        List.of(new InputReads.Applications.Made(closure.at(), List.of()));
                // Applied to nothing, so nothing it states is part of what is read.
                case InputReads.Applications.NoneMade _ -> List.of();
                case InputReads.Applications.MoreThanAreRead _ -> null;
            };
            if (applications == null) {
                return new WrittenOutRead.Stops(new WhyUnread.MoreReadingsThanAreMade());
            }
            InputReads outer = application;
            try {
                for (InputReads.Applications.Made one : applications) {
                    application = one.reads();
                    ofEach.add(whereItIsKept(of(law), one.keptWhere()));
                }
            } finally {
                application = outer;
            }
            return new WrittenOutRead.Each(ofEach);
        }

        /**
         * {@code law}, naming both an element of {@code container} and what {@code block}, the
         * closure, answers, read of each of {@code occurrences}: the element that value, and the
         * closure on the application that hands it that value — the two paired, as the law pairs
         * them, and together with what the occurrence was kept by.
         */
        private WrittenOutRead onTheApplicationHandingEach(DeclaredArgument container,
                                                           List<ReadMeaning.Occurrence> occurrences,
                                                           Denotation closure, Core.Block block,
                                                           LawProposition<DeclaredArgument> law) {
            if (reads.readings() > READINGS.maximum() / occurrences.size()) {
                return new WrittenOutRead.Stops(new WhyUnread.MoreReadingsThanAreMade());
            }
            List<Derivation> ofEach = new ArrayList<>();
            InputReads outer = application;
            try {
                for (ReadMeaning.Occurrence occurrence : occurrences) {
                    Denotation value = occurrence.value();
                    InputReads handing = closure.at().handingTheElement(block,
                            applied.argument(container), value, read.rules().newtypes());
                    if (handing == null) {
                        return new WrittenOutRead.Stops(aClosureNotMet());
                    }
                    elements.put(container, new ElementAt.AValue(value.value(), value.at()));
                    application = handing;
                    ofEach.add(whereItIsKept(of(law), occurrence.keptWhere()));
                }
            } finally {
                elements.remove(container);
                application = outer;
            }
            return new WrittenOutRead.Each(ofEach);
        }


        /**
         * {@code form states 0}, over numbers of the arguments, read as a relation over the
         * quantities a condition is read over.
         */
        private Derivation compared(LawProposition.Compared<DeclaredArgument> compared) {
            Derivation kept = whereAnOperationKeepsIt(compared);
            if (kept != null) {
                return kept;
            }
            Derivation inEachArm = inEachArmOfTheElement(compared);
            if (inEachArm != null) {
                return inEachArm;
            }
            LinearForm<LawNumber<DeclaredArgument>> form = compared.form();
            // An argument chosen by cases is compared on each of them, and one a behavior's call
            // answers through its body, as a comparison the source wrote is
            // ({@link #throughWhatItStopsAt}).
            List<Denotation> numbers = new ArrayList<>();
            form.coefs().keySet().forEach(number -> {
                if (number instanceof LawNumber.AnArgument<DeclaredArgument>(DeclaredArgument at)) {
                    numbers.add(new Denotation(applied.argument(at), reads));
                }
            });
            Inside inside = aWayIn(numbers);
            if (inside != null) {
                return goingIn(inside, reads, new Denotation(e, reads), fixed(e, reads),
                        taking -> new ALawRead(this, taking.apply(reads)).compared(compared));
            }
            // And on each case of how many an argument holds, or a number an argument is takes,
            // where which number that is turns on how the arguments of what made it stand.
            for (LawNumber<DeclaredArgument> number : form.coefs().keySet()) {
                SizedByCases sized = switch (number) {
                    case LawNumber.AnArgument<DeclaredArgument>(DeclaredArgument at) ->
                            measuredByCases(new Denotation(applied.argument(at), reads));
                    case LawNumber.SizeOf<DeclaredArgument>(
                            LawSubject.Argument<DeclaredArgument>(DeclaredArgument at)) -> {
                        SizedByCases made = sizedByCases(applied.argument(at), reads);
                        yield made != null && !sizedInACase.containsKey(made.e()) ? made : null;
                    }
                    // An element that is a value written out is that value, sized as it is.
                    case LawNumber.SizeOf<DeclaredArgument>(
                            LawSubject.ElementOf<DeclaredArgument>(DeclaredArgument at)) -> {
                        SizedByCases made = elements.get(at) instanceof ElementAt.AValue(
                                Core value, InputReads in) ? sizedByCases(value, in) : null;
                        yield made != null && !sizedInACase.containsKey(made.e()) ? made : null;
                    }
                    case LawNumber.SizeOf<DeclaredArgument> _,
                         LawNumber.CodePointsOf<DeclaredArgument> _,
                         LawNumber.HowManyMeet<DeclaredArgument> _,
                         LawNumber.HowManyDifferent<DeclaredArgument> _,
                         LawNumber.SumOver<DeclaredArgument> _ -> null;
                };
                if (sized != null) {
                    return inEachCaseOf(sized, new Denotation(e, reads),
                            () -> compared(compared));
                }
            }
            Map<Quantity.HowManyMeet, Derivation.AComparisonRead.Counted> outer = counting;
            List<Derivation.AComparisonRead.Counted> outerAlike = alike;
            counting = new LinkedHashMap<>();
            alike = new ArrayList<>();
            try {
                return switch (numbers(form)) {
                    case Numbers.NotRead(WhyUnread why) ->
                            leaf(new Derivation.Stopped(why, fixed(e, reads)), e, reads);
                    case Numbers.EachNumber(Map<LawNumber<?>, LinearForm<Quantity>> each) -> {
                        Relation.OneWay<Quantity> stated =
                                Derivation.ALawComparison.relationOf(compared, each);
                        yield leaf(stated != null && pastTheReadings(new Relation.Affine(
                                        stated.form(), stated.proposition()))
                                ? pastTheReadings(fixed(e, reads))
                                : Derivation.ALawComparison.of(compared, each, counting, alike,
                                        READINGS.maximum()), e, reads);
                    }
                };
            } finally {
                counting = outer;
                alike = outerAlike;
            }
        }

        /**
         * {@code compared}, which says only whether a string holds a code point of a class, read
         * as the same statement of what the operation that answered the string was handed, where
         * that operation keeps whether it holds one ({@link Derivation.WhereAnOperationKeepsIt}) —
         * or null where it says more, or the string is no such answer.
         */
        private Derivation whereAnOperationKeepsIt(
                LawProposition.Compared<DeclaredArgument> compared) {
            CodePointClass counted = Derivation.WhereAnOperationKeepsIt.whetherItHoldsOne(compared);
            if (counted == null) {
                return null;
            }
            Map.Entry<LawNumber<DeclaredArgument>, ExactRatio> only =
                    compared.form().coefs().entrySet().iterator().next();
            if (!(only.getKey() instanceof LawNumber.CodePointsOf<DeclaredArgument>(
                    LawSubject.Argument<DeclaredArgument>(DeclaredArgument at), var _))) {
                return null;
            }
            Denotation string = reads.standing(applied.argument(at), read.rules().symbols(),
                    read.rules().newtypes());
            AnOperationApplied made = AnOperationApplied.of(string.value());
            if (made == null || !(DefaultBoundOperationFacts.get()
                    .keepsWhetherItHoldsACodePointOf(made.operation())
                    instanceof BoundOperationFacts.KeptCodePoints kept)
                    || !kept.counted().equals(counted)) {
                return null;
            }
            return new Derivation.WhereAnOperationKeepsIt(compared, made.operation(),
                    new ALawRead(made, string.value(), string.at()).of(
                            Derivation.WhereAnOperationKeepsIt.saidOfWhatItWasHanded(compared,
                                    kept)));
        }

        /**
         * {@code compared} in each arm of the choice an element it numbers is, where that element
         * is a value chosen by a fork — an {@code if} or a {@code match} a closure answered with:
         * in each arm the element is the value that arm answers, and the comparison is read of
         * that. Null where no element it numbers is such a value.
         */
        private Derivation inEachArmOfTheElement(
                LawProposition.Compared<DeclaredArgument> compared) {
            for (LawNumber<DeclaredArgument> number : compared.form().coefs().keySet()) {
                DeclaredArgument container = switch (number) {
                    case LawNumber.CodePointsOf<DeclaredArgument>(
                            LawSubject.ElementOf<DeclaredArgument>(DeclaredArgument at), var _) ->
                            at;
                    case LawNumber.SizeOf<DeclaredArgument>(
                            LawSubject.ElementOf<DeclaredArgument>(DeclaredArgument at)) -> at;
                    default -> null;
                };
                if (container == null || !(elements.get(container) instanceof ElementAt.AValue(
                        Core value, InputReads in))) {
                    continue;
                }
                Denotation stands = in.standing(value, read.rules().symbols(),
                        read.rules().newtypes());
                switch (Core.withoutStanding(stands.value())) {
                    case Core.If iff -> {
                        return new Derivation.IfThenElse(
                                observe(iff.cond(), AnswerAspect.TRUTH, stands.at()),
                                asTheElement(container, iff.then(), stands.at(), compared),
                                asTheElement(container, iff.els(), stands.at(), compared));
                    }
                    case Core.Match match -> {
                        return armsOf(match, stands.at(), (body, inside) ->
                                asTheElement(container, body, inside, compared));
                    }
                    default -> { }
                }
            }
            return null;
        }

        /** {@code compared} read where the element of {@code container} is {@code value}. */
        private Derivation asTheElement(DeclaredArgument container, Core value, InputReads in,
                                        LawProposition.Compared<DeclaredArgument> compared) {
            ElementAt was = elements.put(container, new ElementAt.AValue(value, in));
            try {
                return compared(compared);
            } finally {
                elements.put(container, was);
            }
        }


        /** The argument a number of a law is of. */
        private static DeclaredArgument argumentOf(LawNumber<DeclaredArgument> number) {
            return switch (number) {
                case LawNumber.AnArgument<DeclaredArgument>(DeclaredArgument at) -> at;
                case LawNumber.SizeOf<DeclaredArgument>(LawSubject<DeclaredArgument> of) ->
                        argumentOf(of);
                case LawNumber.CodePointsOf<DeclaredArgument>(
                        LawSubject<DeclaredArgument> of, var _) -> argumentOf(of);
                case LawNumber.HowManyMeet<DeclaredArgument>(DeclaredArgument at, var _) -> at;
                case LawNumber.HowManyDifferent<DeclaredArgument>(DeclaredArgument at, var _) -> at;
                case LawNumber.SumOver<DeclaredArgument>(DeclaredArgument at, var _) -> at;
            };
        }

        /** The argument a subject of a law is of. */
        private static DeclaredArgument argumentOf(LawSubject<DeclaredArgument> of) {
            return switch (of) {
                case LawSubject.Argument<DeclaredArgument>(DeclaredArgument at) -> at;
                case LawSubject.ElementOf<DeclaredArgument>(DeclaredArgument at) -> at;
                case LawSubject.WhatTheClosureAnswers<DeclaredArgument>(DeclaredArgument at) -> at;
                case LawSubject.KeyOf<DeclaredArgument>(DeclaredArgument at) -> at;
                case LawSubject.AnswerOf<DeclaredArgument> _ -> throw namedInNoLaw(of);
            };
        }

        /** What of its argument a number of a law is, in the order the kinds are declared in. */
        private static int whatOfIt(LawNumber<DeclaredArgument> number) {
            return switch (number) {
                case LawNumber.AnArgument<DeclaredArgument> _ -> 0;
                case LawNumber.SizeOf<DeclaredArgument>(LawSubject<DeclaredArgument> of) ->
                        switch (of) {
                            case LawSubject.Argument<DeclaredArgument> _ -> 1;
                            case LawSubject.ElementOf<DeclaredArgument> _ -> 2;
                            case LawSubject.WhatTheClosureAnswers<DeclaredArgument> _ -> 3;
                            case LawSubject.KeyOf<DeclaredArgument> _ -> 4;
                            case LawSubject.AnswerOf<DeclaredArgument> _ -> throw namedInNoLaw(of);
                        };
                case LawNumber.HowManyMeet<DeclaredArgument> _ -> 5;
                case LawNumber.HowManyDifferent<DeclaredArgument> _ -> 6;
                case LawNumber.SumOver<DeclaredArgument> _ -> 7;
                case LawNumber.CodePointsOf<DeclaredArgument> _ -> 8;
            };
        }

        /**
         * {@code form}, a number of the arguments, as a form over the quantities a condition is
         * read over: the law's form over what each of its numbers was read as, worked out where
         * a law's comparison is ({@link Derivation.ALawComparison#formOf}).
         */
        Sized number(LinearForm<LawNumber<DeclaredArgument>> form) {
            return switch (numbers(form)) {
                case Numbers.NotRead(WhyUnread why) -> new Sized.NotSized(why);
                case Numbers.EachNumber(var each) ->
                        switch (Derivation.ALawComparison.formOf(form, each)) {
                            case ExactAnswer.Held<LinearForm<Quantity>>(var held) ->
                                    new Sized.AsAForm(held);
                            case ExactAnswer.Unheld<LinearForm<Quantity>>(var why) ->
                                    new Sized.NotSized(new WhyUnread.ANumberNotHeld(why));
                        };
            };
        }

        /**
         * What each number {@code form} names was read as, or why one was not — or why the form
         * over them is not held. Walked by the argument each number is of, and then by what of it
         * the number is, so that where two numbers have no form, which one the law is said to stop
         * at is the law's and not the order a map keeps its numbers in.
         */
        private Numbers numbers(LinearForm<LawNumber<DeclaredArgument>> form) {
            List<LawNumber<DeclaredArgument>> inOrder = new ArrayList<>(form.coefs().keySet());
            inOrder.sort(Comparator.comparingInt(
                            (LawNumber<DeclaredArgument> each) -> argumentOf(each).position())
                    .thenComparingInt(ALawRead::whatOfIt));
            Map<LawNumber<?>, LinearForm<Quantity>> out = new LinkedHashMap<>();
            for (LawNumber<DeclaredArgument> number : inOrder) {
                switch (atom(number)) {
                    case Sized.AsAForm(LinearForm<Quantity> each) -> out.put(number, each);
                    case Sized.NotSized(WhyUnread why) -> {
                        return new Numbers.NotRead(why);
                    }
                }
            }
            return Derivation.ALawComparison.formOf(form, out)
                    instanceof ExactAnswer.Unheld<LinearForm<Quantity>>(var why)
                    ? new Numbers.NotRead(new WhyUnread.ANumberNotHeld(why))
                    : new Numbers.EachNumber(out);
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
                                        case ElementAt.AValue(Core value, InputReads in) ->
                                                sizeOf(value, in);
                                        case ElementAt.AtASubject(DecisionSubject container) ->
                                                sizedAt(container.element());
                                        case ElementAt.AFiledElement(TermPath list,
                                                                     Core.Block _) ->
                                                sizedAt(new DecisionSubject.AnInput(
                                                        list.element()));
                                        case ElementAt.APiece _, ElementAt.AnEntry _,
                                             ElementAt.OfAnAnswerEveryElementOfWhichIs _ ->
                                                new Sized.NotSized(new WhyUnread.AtNoPosition(
                                                        WhyUnread.AtNoPosition.Place.SUBJECT));
                                    };
                            case LawSubject.WhatTheClosureAnswers<DeclaredArgument>(
                                    DeclaredArgument at) -> {
                                Denotation answered = whatTheClosureAnswers(at);
                                yield answered != null ? sizeOf(answered.value(), answered.at())
                                        : new Sized.NotSized(aClosureNotMet());
                            }
                            case LawSubject.KeyOf<DeclaredArgument>(DeclaredArgument at) -> {
                                DecisionSubject key = keyAt(at);
                                yield key != null ? sizedAt(key) : new Sized.NotSized(
                                        new WhyUnread.AtNoPosition(
                                                WhyUnread.AtNoPosition.Place.SUBJECT));
                            }
                            case LawSubject.AnswerOf<DeclaredArgument> _ -> throw namedInNoLaw(of);
                        };
                case LawNumber.CodePointsOf<DeclaredArgument>(
                        LawSubject<DeclaredArgument> of, CodePointClass counted) ->
                        codePointsOf(of, counted);
                case LawNumber.HowManyMeet<DeclaredArgument> counted -> count(counted);
                case LawNumber.HowManyDifferent<DeclaredArgument>(DeclaredArgument at,
                                                                  var ofTheElement) ->
                        different(at, ofTheElement);
                case LawNumber.SumOver<DeclaredArgument>(DeclaredArgument at, var ofTheElement) ->
                        sumOver(at, ofTheElement);
            };
        }

        /**
         * How many of the code points of the string {@code of} names are in {@code counted}, where
         * the string stands at a position of the input.
         *
         * <p>A number of that position and no other: the string's own length is a second one, and
         * a rule over both is one over two numbers of one place.
         */
        private Sized codePointsOf(LawSubject<DeclaredArgument> of, CodePointClass counted) {
            // A value the element is is read as itself, where it was given.
            if (of instanceof LawSubject.ElementOf<DeclaredArgument>(DeclaredArgument container)
                    && elements.get(container) instanceof ElementAt.AValue(Core value,
                                                                          InputReads in)) {
                return codePointsOfTheValue(value, in, counted);
            }
            if (of instanceof LawSubject.Argument<DeclaredArgument>(DeclaredArgument argument)) {
                return codePointsOfTheValue(applied.argument(argument), reads, counted);
            }
            TermPath at = switch (of) {
                case LawSubject.ElementOf<DeclaredArgument>(DeclaredArgument container) ->
                        elements.get(container) instanceof ElementAt.AtASubject(
                                DecisionSubject.AnInput(TermPath held)) ? held.element() : null;
                case LawSubject.KeyOf<DeclaredArgument>(DeclaredArgument container) ->
                        keyAt(container) instanceof DecisionSubject.AnInput(TermPath key)
                                ? key : null;
                case LawSubject.Argument<DeclaredArgument> _,
                     LawSubject.WhatTheClosureAnswers<DeclaredArgument> _ -> null;
                case LawSubject.AnswerOf<DeclaredArgument> _ -> throw namedInNoLaw(of);
            };
            if (at == null) {
                // A piece of a string a split left stands at no position, and its count is the
                // one of a piece: what the statement about some piece it is read inside comes to
                // for the string is that statement's to say ({@link #somePiece}).
                return of instanceof LawSubject.ElementOf<DeclaredArgument>(
                        DeclaredArgument container)
                        && elements.get(container) instanceof ElementAt.APiece
                        ? new Sized.AsAForm(LinearForm.atom(
                                new Quantity.CodePointsOfAPiece(counted)))
                        : new Sized.NotSized(new WhyUnread.AtNoPosition(
                                WhyUnread.AtNoPosition.Place.SUBJECT));
            }
            return codePointsAt(at, counted);
        }

        /**
         * How many of the code points of {@code value}, read in {@code in}, are in
         * {@code counted}: of the string at a position, where it stands at one; as many as are,
         * of a string written out; and of a piece, where it is one ({@link #somePiece}).
         */
        private Sized codePointsOfTheValue(Core value, InputReads in, CodePointClass counted) {
            if (in.pathOf(value, read.rules().newtypes()) instanceof PathResolution.At(TermPath at)) {
                return codePointsAt(at, counted);
            }
            Denotation standing = in.standing(value, read.rules().symbols(),
                    read.rules().newtypes());
            if (Core.withoutStanding(standing.value()) instanceof Core.Str written) {
                return new Sized.AsAForm(LinearForm.constant(ExactRatio.of(
                        written.value().codePoints().filter(counted::contains).count())));
            }
            return pieceThatIs(value, in) != null
                    ? new Sized.AsAForm(LinearForm.atom(new Quantity.CodePointsOfAPiece(counted)))
                    : new Sized.NotSized(new WhyUnread.AtNoPosition(
                            WhyUnread.AtNoPosition.Place.SUBJECT));
        }

        /** How many of the code points of the string at {@code at} are in {@code counted}. */
        private Sized codePointsAt(TermPath at, CodePointClass counted) {
            Type type = read.domain().typeAt(at, read.rules());
            NumericTerm.CodePointClassCount term = type == null ? null
                    : NumericTerm.CodePointClassCount.of(at, counted, type, read.rules().inners());
            return term == null ? new Sized.NotSized(new WhyUnread.NoMeasureOfItsSize())
                    : new Sized.AsAForm(LinearForm.atom(new DecisionAtom.OfTheInput(term)));
        }

        /**
         * Where the elements of the argument {@code at} stand, beneath what only put them in
         * another order and through every walk answering one value for each of them — or null
         * where they stand at no position.
         *
         * <p>The same reading {@link #count} makes, so that what is asked of the elements of a
         * container does not turn on which number of them it is. How many of them there are, what
         * a number of each adds up to and how many differ are three numbers over one container.
         *
         * @param counting whether how often a value stands is asked, which a set made of what a
         *                 closure answered does not say
         */
        private Located elementsOf(DeclaredArgument at, boolean counting) {
            Core given = applied.argument(at);
            Denotation container = reads.standing(given, read.rules().symbols(),
                    read.rules().newtypes());
            return elementsOf(given, container, beneath(container, counting), counting);
        }

        /**
         * The same, of {@code given} standing as {@code container}, with what is beneath it read
         * off already.
         */
        private Located elementsOf(Core given, Denotation container, Beneath beneath,
                                   boolean counting) {
            Core over = beneath == null ? given : beneath.at().value();
            InputReads in = beneath == null ? reads : beneath.at().at();
            return locate(beneath == null ? container : beneath.at(), over, in,
                    beneath == null ? List.of() : beneath.kept(), counting);
        }

        /**
         * How many different values {@code ofTheElement} comes to over the elements of the
         * container at {@code at}, where they stand at a position and what is taken of each stands
         * at one inside it.
         *
         * <p>Of every element and not of some: a filter that kept the elements meeting something
         * leaves a number of the ones it kept, which no quantity of the container says. And a
         * closure's answer on an element is a place only where it reads one inside that element —
         * {@code .currency} is {@code fs[*].currency}, and a value worked out of it is none.
         */
        private Sized different(DeclaredArgument at, LawSubject<DeclaredArgument> ofTheElement) {
            Sized written = differentWrittenOut(at, ofTheElement);
            if (written != null) {
                return written;
            }
            Located located = elementsOf(at, false);
            if (located == null || !located.kept().isEmpty()) {
                return new Sized.NotSized(
                        new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.CONTAINER));
            }
            // How many different values the elements come to is a number of the input's own
            // places, which what a dependency answered has none of.
            if (!(located.held() instanceof DecisionSubject.AnInput(TermPath held))) {
                return new Sized.NotSized(
                        new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.CONTAINER));
            }
            TermPath each = switch (ofTheElement) {
                case LawSubject.ElementOf<DeclaredArgument> _ -> switch (located.each()) {
                    case ElementAt.AtASubject(DecisionSubject.AnInput(TermPath container)) ->
                            container.element();
                    case ElementAt.AtASubject(DecisionSubject.AnAnswer _) -> null;
                    case ElementAt.AFiledElement(TermPath list, Core.Block _) -> list.element();
                    case ElementAt.AValue(Core value, InputReads in) ->
                            in.pathOf(value, read.rules().newtypes())
                                    instanceof PathResolution.At(TermPath inside)
                                    && inside.isAtOrUnder(held.element()) ? inside : null;
                    case ElementAt.APiece _, ElementAt.AnEntry _,
                         ElementAt.OfAnAnswerEveryElementOfWhichIs _ -> null;
                };
                // The key of an entry is a place of a map, which the declarations say where there
                // is one. Where the entries are a list's, a component of each is no place of an
                // input at all.
                case LawSubject.KeyOf<DeclaredArgument> _ ->
                        located.each() instanceof ElementAt.AtASubject(
                                DecisionSubject.AnInput(TermPath map))
                                && read.domain().typeAt(map.key(), read.rules()) != null
                                ? map.key() : null;
                // What a closure answers stands at no position a row writes.
                case LawSubject.WhatTheClosureAnswers<DeclaredArgument> _,
                     LawSubject.Argument<DeclaredArgument> _ -> null;
                case LawSubject.AnswerOf<DeclaredArgument> _ -> throw namedInNoLaw(ofTheElement);
            };
            return each == null ? new Sized.NotSized(
                    new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT))
                    : new Sized.AsAForm(LinearForm.atom(new Quantity.HowManyDifferent(
                            new DecisionSubject.AnInput(held), new DecisionSubject.AnInput(each))));
        }

        /**
         * How many different values {@code ofTheElement} comes to over the elements of the
         * container at {@code at}, where the container is written out and what is taken of each
         * element is a value written out — or null where it is not, which leaves the elements to
         * be looked for at a position.
         *
         * <p>A number and not a quantity: every value is written, so how many differ is the same on
         * every row. Only where every element there on some row is there on every row
         * ({@link #there}). One kept by a truth that turns on the row is counted where the truth
         * holds, and the count would turn on which of them do.
         */
        private Sized differentWrittenOut(DeclaredArgument at,
                                          LawSubject<DeclaredArgument> ofTheElement) {
            Denotation container = reads.standing(applied.argument(at), read.rules().symbols(),
                    read.rules().newtypes());
            List<ReadMeaning.Occurrence> occurrences;
            switch (eachValue(container)) {
                case WrittenOutElements.Walked.Each each -> occurrences = there(each);
                case WrittenOutElements.Walked.PastTheFigure _ -> {
                    return new Sized.NotSized(new WhyUnread.MoreReadingsThanAreMade());
                }
                case WrittenOutElements.Walked.NotWrittenOut _ -> {
                    return null;
                }
            }
            if (occurrences.stream().anyMatch(each -> !each.keptWhere().isEmpty())) {
                return null;
            }
            Set<Object> different = new HashSet<>();
            for (ReadMeaning.Occurrence occurrence : occurrences) {
                Denotation taken = takenOf(at, ofTheElement, occurrence.value());
                Object value = taken == null ? null : writtenValueOf(taken);
                if (value == null) {
                    return null;
                }
                different.add(value);
            }
            return new Sized.AsAForm(LinearForm.constant(ExactRatio.of(different.size())));
        }

        /**
         * What {@code ofTheElement} takes of the element of the container at {@code at} that is
         * {@code value}: the value itself, or the closure's answer on the application handing it
         * that value — or null where it takes something else.
         */
        private Denotation takenOf(DeclaredArgument at, LawSubject<DeclaredArgument> ofTheElement,
                                  Denotation value) {
            return switch (ofTheElement) {
                case LawSubject.ElementOf<DeclaredArgument> _ -> value;
                case LawSubject.WhatTheClosureAnswers<DeclaredArgument>(DeclaredArgument named) -> {
                    Denotation closure = reads.denotes(applied.argument(named),
                            read.rules().symbols(), read.rules().newtypes());
                    if (!(Core.withoutStanding(closure.value()) instanceof Core.Block block)) {
                        yield null;
                    }
                    InputReads handing = closure.at().handingTheElement(block,
                            applied.argument(at), value, read.rules().newtypes());
                    yield handing == null ? null : new Denotation(block.body(), handing);
                }
                case LawSubject.KeyOf<DeclaredArgument> _,
                     LawSubject.Argument<DeclaredArgument> _ -> null;
                case LawSubject.AnswerOf<DeclaredArgument> _ -> throw namedInNoLaw(ofTheElement);
            };
        }

        /**
         * The value {@code e} stands as, where it is one written with nothing in it that two values
         * are told apart by — a case with no fields, a whole number, a string, a truth — or null.
         * Two of these are one value exactly where they are equal.
         */
        private Object writtenValueOf(Denotation e) {
            return switch (Core.withoutStanding(e.at().standing(e.value(), read.rules().symbols(),
                    read.rules().newtypes()).value())) {
                case Core.UnitValue unit -> unit.data();
                case Core.Int number -> number.value();
                case Core.Str text -> text.value();
                case Core.Bool truth -> truth.value();
                case null, default -> null;
            };
        }

        /**
         * What {@code ofTheElement}, a number of each element of the container at {@code at}, adds
         * up to over them, where the elements stand at a position ({@link #elementsOf}) or are
         * values the source wrote out, or pieces an operation put together of such values.
         *
         * <p>Of every element, as {@link #different} is: a number over some of them is no sum a
         * quantity of the container states. So of the occurrences written out, only where every
         * one there on some row is there on every row ({@link #there}); a sum of the ones a truth
         * keeps on the row would turn on which of them it keeps.
         */
        private Sized sumOver(DeclaredArgument at, LawNumber<DeclaredArgument> ofTheElement) {
            Core given = applied.argument(at);
            Denotation container = reads.standing(given, read.rules().symbols(),
                    read.rules().newtypes());
            WrittenOutElements.Walked written = eachValue(container);
            Beneath beneath = null;
            if (written instanceof WrittenOutElements.Walked.NotWrittenOut) {
                beneath = beneath(container, true);
                if (beneath != null) {
                    written = eachValue(beneath.at());
                }
            }
            switch (written) {
                case WrittenOutElements.Walked.PastTheFigure _ -> {
                    return new Sized.NotSized(new WhyUnread.MoreReadingsThanAreMade());
                }
                case WrittenOutElements.Walked.Each each -> {
                    List<ReadMeaning.Occurrence> occurrences = there(each);
                    if ((beneath != null && !beneath.kept().isEmpty())
                            || occurrences.stream().anyMatch(one -> !one.keptWhere().isEmpty())) {
                        return new Sized.NotSized(
                                new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.CONTAINER));
                    }
                    return sumOverWrittenOut(at,
                            occurrences.stream().map(ReadMeaning.Occurrence::value).toList(),
                            ofTheElement);
                }
                case WrittenOutElements.Walked.NotWrittenOut _ -> {
                }
            }
            Located located = elementsOf(given, container, beneath, true);
            if (located == null || !located.kept().isEmpty()) {
                return new Sized.NotSized(
                        new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.CONTAINER));
            }
            // A sum over the elements is a number of the input's own places, which what a
            // dependency answered has none of.
            if (!(located.held() instanceof DecisionSubject.AnInput held)) {
                return new Sized.NotSized(
                        new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.CONTAINER));
            }
            if (!quantifying.add(held)) {
                return new Sized.NotSized(new WhyUnread.TwoElementsOfOneContainer());
            }
            elements.put(at, located.each());
            Sized each;
            try {
                each = number(LinearForm.atom(ofTheElement));
            } finally {
                elements.remove(at);
                quantifying.remove(held);
            }
            if (!(each instanceof Sized.AsAForm(LinearForm<Quantity> form))) {
                return each;
            }
            // What every element adds alike is that many times how many elements there are, which
            // is asked only where there is such a part.
            DecisionAtom size = form.constant().signum() == 0 ? null : sizeOfSubject(held, null);
            LinearForm<Quantity> summed = Quantity.SumOver.over(held, form, size);
            return summed == null ? new Sized.NotSized(new WhyUnread.NoMeasureOfItsSize())
                    : new Sized.AsAForm(summed);
        }

        /**
         * What {@code ofTheElement} adds up to over {@code values}, the values a container of the
         * argument {@code at} was written out with: its number of each, read with the element that
         * value and a closure it names on the application handing it that value, added together.
         */
        private Sized sumOverWrittenOut(DeclaredArgument at, List<Denotation> values,
                                        LawNumber<DeclaredArgument> ofTheElement) {
            if (reads.readings() * values.size() > READINGS.maximum()) {
                return new Sized.NotSized(new WhyUnread.MoreReadingsThanAreMade());
            }
            DeclaredArgument named = closureIn(ofTheElement);
            Denotation closure = named == null ? null : reads.denotes(applied.argument(named),
                    read.rules().symbols(), read.rules().newtypes());
            Core.Block block = closure != null
                    && Core.withoutStanding(closure.value()) instanceof Core.Block written
                    ? written : null;
            if (closure != null && block == null) {
                return new Sized.NotSized(aClosureNotMet());
            }
            LinearForm<Quantity> total = LinearForm.constant(ExactRatio.ZERO);
            InputReads outer = application;
            try {
                for (Denotation value : values) {
                    if (block != null) {
                        InputReads handing = closure.at().handingTheElement(block,
                                applied.argument(at), value, read.rules().newtypes());
                        if (handing == null) {
                            return new Sized.NotSized(aClosureNotMet());
                        }
                        application = handing;
                    }
                    elements.put(at, new ElementAt.AValue(value.value(), value.at()));
                    Sized each = number(LinearForm.atom(ofTheElement));
                    if (!(each instanceof Sized.AsAForm(LinearForm<Quantity> form))) {
                        return each;
                    }
                    switch (total.plus(form)) {
                        case ExactAnswer.Held<LinearForm<Quantity>>(var sum) -> total = sum;
                        case ExactAnswer.Unheld<LinearForm<Quantity>>(var why) -> {
                            return new Sized.NotSized(new WhyUnread.ANumberNotHeld(why));
                        }
                    }
                }
            } finally {
                elements.remove(at);
                application = outer;
            }
            return new Sized.AsAForm(total);
        }

        /** How many what stands at {@code at} holds, as a number of the input. A place inside what
         *  a dependency answered has no type here to be counted by, and is none the declarations
         *  measure. */
        private Sized sizedAt(DecisionSubject at) {
            DecisionAtom size = sizeOfSubject(at, null);
            return size == null ? new Sized.NotSized(new WhyUnread.NoMeasureOfItsSize())
                    : new Sized.AsAForm(LinearForm.atom(size));
        }

        /** How many elements of a container meet a statement, as one count of the quantities a
         *  relation is written over. */
        private Sized count(LawNumber.HowManyMeet<DeclaredArgument> counted) {
            Core given = applied.argument(counted.container());
            Denotation container = reads.standing(given, read.rules().symbols(),
                    read.rules().newtypes());
            // Of a container written out, or put together of pieces of one, every occurrence is
            // counted where it is kept.
            WrittenOutElements.Walked values = eachValue(container);
            Beneath beneath = null;
            if (values instanceof WrittenOutElements.Walked.NotWrittenOut) {
                // Another order of the same elements has as many of them meeting a statement, and
                // what an operation kept of them has as many as meet that and what it kept by.
                beneath = beneath(container, true);
                if (beneath != null) {
                    container = beneath.at();
                    values = eachValue(container);
                }
            }
            Core over = beneath == null ? given : beneath.at().value();
            InputReads in = beneath == null ? reads : beneath.at().at();
            List<Kept> kept = beneath == null ? List.of() : beneath.kept();
            if (values instanceof WrittenOutElements.Walked.PastTheFigure) {
                return new Sized.NotSized(new WhyUnread.MoreReadingsThanAreMade());
            }
            // Of values written out, how many meet the statement is how many of the statements
            // about each of them hold: a number where each of them settles whether it does, and
            // beside that how many of the rest hold, which is read as which of them do where it is
            // compared.
            if (values instanceof WrittenOutElements.Walked.Each && !kept.isEmpty()) {
                return new Sized.NotSized(
                        new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.CONTAINER));
            }
            if (values instanceof WrittenOutElements.Walked.Each walked) {
                List<ReadMeaning.Occurrence> occurrences = there(walked);
                return switch (ofEachWrittenOut(counted.container(), occurrences,
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
                        // How many choices of which of them hold a comparison is read as turns on
                        // the number it is compared with, and is held to the readings of one
                        // condition where it is ({@link #aRelation}).
                        yield new Sized.AsAForm(new LinearForm<>(settled.constant(),
                                Map.of(new Quantity.HowManyHold(unsettled), ExactRatio.ONE)));
                    }
                };
            }
            // At a position, or a walk's answer over one: as many of its elements meet the
            // statement as elements there whose step's answer does.
            Located located = counting == null ? null : locate(container, over, in, kept, true);
            if (located == null) {
                return new Sized.NotSized(
                        new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.CONTAINER));
            }
            DecisionSubject heldAt = located.held();
            Derivation answered = aboutAnElement(counted.container(), heldAt, located.each(),
                    counted.ofTheElement());
            if (answered == null) {
                return new Sized.NotSized(new WhyUnread.TwoElementsOfOneContainer());
            }
            answered = alsoWhatWasKept(answered, located.kept());
            Proposition element = trying.of(answered);
            WhyUnread stopped = Proposition.firstStopIn(element);
            if (stopped != null) {
                return new Sized.NotSized(stopped);
            }
            // What is the same for every element counts all of them or none.
            if (!element.mayTurnOnAnElementOf(heldAt)) {
                if (element instanceof Proposition.Always(boolean holds)) {
                    if (alike != null) {
                        alike.add(new Derivation.AComparisonRead.Counted(heldAt, answered));
                    }
                    DecisionAtom size = sizeOfSubject(heldAt, located.heldType());
                    return !holds ? new Sized.AsAForm(LinearForm.constant(ExactRatio.ZERO))
                            : size == null ? new Sized.NotSized(new WhyUnread.NoMeasureOfItsSize())
                            : new Sized.AsAForm(LinearForm.atom(size));
                }
                return new Sized.NotSized(new WhyUnread.NotArithmetic());
            }
            Quantity.HowManyMeet count = new Quantity.HowManyMeet(heldAt, element);
            counting.putIfAbsent(count, new Derivation.AComparisonRead.Counted(heldAt, answered));
            return new Sized.AsAForm(LinearForm.atom(count));
        }
    }

    /**
     * Why what a closure answers was read as nothing, where it stands for no block whose body the
     * reading can read.
     *
     * <p>A closure an operation is handed is written where it is handed or is a name for one — the
     * language refuses any other — and a name is read through to what it was given; so one standing
     * for no block is a body the reading did not meet.
     */
    private static WhyUnread aClosureNotMet() {
        return new WhyUnread.NotMetByTheReading();
    }

    /** Whether {@code law} says the element is the same value as another. */
    private static boolean statesTheValueOfTheElement(LawProposition<DeclaredArgument> law) {
        return switch (law) {
            case LawProposition.Same<DeclaredArgument> _ -> true;
            case LawProposition.All<DeclaredArgument> all -> all.parts().stream()
                    .anyMatch(Pullback::statesTheValueOfTheElement);
            case LawProposition.Any<DeclaredArgument> any -> any.parts().stream()
                    .anyMatch(Pullback::statesTheValueOfTheElement);
            case LawProposition.SomeElement<DeclaredArgument> some ->
                    statesTheValueOfTheElement(some.ofTheElement());
            case LawProposition.Always<DeclaredArgument> _,
                 LawProposition.Compared<DeclaredArgument> _,
                 LawProposition.Observed<DeclaredArgument> _ -> false;
        };
    }

    /** The closure {@code law} names what it answers of, or null where it names none. */
    private static DeclaredArgument closureIn(LawProposition<DeclaredArgument> law) {
        return switch (law) {
            case LawProposition.Always<DeclaredArgument> _,
                 LawProposition.Same<DeclaredArgument> _ -> null;
            case LawProposition.Compared<DeclaredArgument> compared -> {
                for (LawNumber<DeclaredArgument> number : compared.form().coefs().keySet()) {
                    DeclaredArgument closure = closureIn(number);
                    if (closure != null) {
                        yield closure;
                    }
                }
                yield null;
            }
            case LawProposition.All<DeclaredArgument> all -> closureIn(all.parts());
            case LawProposition.Any<DeclaredArgument> any -> closureIn(any.parts());
            case LawProposition.Observed<DeclaredArgument> observed ->
                    observed.of() instanceof LawSubject.WhatTheClosureAnswers<DeclaredArgument>(
                            DeclaredArgument closure) ? closure : null;
            case LawProposition.SomeElement<DeclaredArgument> some ->
                    closureIn(some.ofTheElement());
        };
    }

    /** The closure {@code number} names what it answers of, or null where it names none. */
    private static DeclaredArgument closureIn(LawNumber<DeclaredArgument> number) {
        return switch (number) {
            case LawNumber.AnArgument<DeclaredArgument> _ -> null;
            case LawNumber.HowManyDifferent<DeclaredArgument>(var _, var of) ->
                    of instanceof LawSubject.WhatTheClosureAnswers<DeclaredArgument>(
                            DeclaredArgument closure) ? closure : null;
            case LawNumber.SizeOf<DeclaredArgument>(var of) ->
                    of instanceof LawSubject.WhatTheClosureAnswers<DeclaredArgument>(
                            DeclaredArgument closure) ? closure : null;
            case LawNumber.CodePointsOf<DeclaredArgument>(var of, var _) ->
                    of instanceof LawSubject.WhatTheClosureAnswers<DeclaredArgument>(
                            DeclaredArgument closure) ? closure : null;
            case LawNumber.HowManyMeet<DeclaredArgument>(var _, var ofTheElement) ->
                    closureIn(ofTheElement);
            case LawNumber.SumOver<DeclaredArgument>(var _, var ofTheElement) ->
                    closureIn(ofTheElement);
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
                        case LawNumber.CodePointsOf<DeclaredArgument>(var of, var _) ->
                                of.equals(new LawSubject.ElementOf<>(container));
                        case LawNumber.HowManyMeet<DeclaredArgument> inner ->
                                namesTheElement(inner.ofTheElement(), container);
                        case LawNumber.HowManyDifferent<DeclaredArgument>(var _, var of) ->
                                of.equals(new LawSubject.ElementOf<>(container));
                        case LawNumber.SumOver<DeclaredArgument>(var _, var of) ->
                                namesTheElement(new LawProposition.Compared<>(
                                        LinearForm.atom(of), Rel.EQ), container);
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
    private Derivation holdsSomethingAt(DecisionSubject held, Type type) {
        DecisionAtom count = sizeOfSubject(held, type);
        return count == null ? null : new Derivation.SizeAboveNought(count);
    }

    /**
     * How many what stands at {@code held} holds, as a number of the quantities a condition is read
     * over: a count of the input where it stands at a position, and the count of what a dependency
     * answered where it is that. Null where no type measures it.
     *
     * @param type what stands there, which an answer's count is taken by; the input's own type is
     *             what the declarations say of the position
     */
    private DecisionAtom sizeOfSubject(DecisionSubject held, Type type) {
        return switch (held) {
            case DecisionSubject.AnInput(TermPath at) -> {
                NumericTerm.TakenOf size = sizeAt(at);
                yield size == null ? null : new DecisionAtom.OfTheInput(size);
            }
            case DecisionSubject.AnAnswer answer -> {
                ValueName.Stdlib measure = type == null ? null
                        : NumericMeasures.takenOf(type, read.rules().inners());
                yield measure == null ? null
                        : new DecisionAtom.TakenOfAnAnswer(measure, TakenArguments.NONE, answer,
                                type);
            }
        };
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
        // vary: nothing it compares is followed back to the input.
        if (fixed) {
            return new Derivation.Stopped(
                    new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT), true);
        }
        Denotation left = new Denotation(comparison.left(), reads);
        Denotation right = new Denotation(comparison.right(), reads);
        // One whose arithmetic stops at a value the reading goes into is read through it, by the
        // rule before this one.
        if (aWayIn(List.of(left, right)) != null) {
            return null;
        }
        return overQuantities(left, right, comparison.claim().statedRelation());
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
        List<Derivation.AComparisonRead.Counted> outerAlike = alike;
        ElementsMet outerElements = elementsMet;
        counting = new LinkedHashMap<>();
        alike = null;
        elementsMet = new ElementsMet();
        try {
            return overQuantitiesCounting(left, right, states);
        } finally {
            counting = outer;
            alike = outerAlike;
            elementsMet = outerElements;
        }
    }

    /** The numbers of the input {@code forms} are over, the ones what an operation answers is
     *  made of among them, which is what a comparison read through them names however much of it
     *  cancels. */
    private static Set<NumericTerm> ofTheInputIn(List<LinearForm<Quantity>> forms) {
        Set<NumericTerm> out = new LinkedHashSet<>();
        for (LinearForm<Quantity> form : forms) {
            for (Quantity atom : form.coefs().keySet()) {
                if (atom instanceof DecisionAtom.OfTheInput(NumericTerm term)) {
                    out.add(term);
                } else if (atom instanceof Quantity.WhatAnOperationAnswers answers) {
                    out.addAll(answers.positionsItIsMadeOf());
                }
            }
        }
        return out;
    }

    /**
     * {@code left states right} over the quantities a condition is read over.
     *
     * <p>A side the reading stopped in may be what an operation answers of the input
     * ({@link Quantity.WhatAnOperationAnswers}), and is read as that where the two sides come to
     * one value against another made of positions apart, or to one value on both
     * ({@link #answeredApart}). A side stopped in is one no form was read of, or a name for a value
     * whose making the reading stopped at, which is the same value under a name. A constant or a
     * sum beside such an answer is a line on it, which nothing here draws, so the side stays where
     * the reading stopped.
     */
    private Derivation overQuantitiesCounting(Denotation left, Denotation right, Rel states) {
        List<LinearForm<Quantity>> sides = new ArrayList<>();
        List<Denotation> calls = new ArrayList<>();
        Derivation unread = null;
        for (Denotation side : List.of(left, right)) {
            switch (AffineForms.outcome(side.value(), side.at(), quantities())) {
                case AffineForms.Outcome.Composed<Quantity, InputReads>(var form) -> {
                    sides.add(form);
                    calls.add(madeOfWhereItStopped(form) ? callOf(side) : null);
                }
                case AffineForms.Outcome.StoppedAt<Quantity, InputReads> stopped -> {
                    // A comparison of two elements of one container is read of neither: they
                    // stand at one position, and a form would hold them as one number.
                    Derivation stop = new Derivation.Stopped(elementsMet.crowded()
                            ? new WhyUnread.TwoElementsOfOneContainer() : noFormOf(stopped), false);
                    // Only the call of an operation may be what one answers, and nothing is
                    // read past any other stop.
                    Denotation call = elementsMet.crowded() ? null : callOf(side);
                    if (call == null) {
                        return unread != null ? unread : stop;
                    }
                    unread = unread != null ? unread : stop;
                    sides.add(null);
                    calls.add(call);
                }
            }
        }
        LinearForm<Quantity> form = null;
        if (calls.stream().anyMatch(Objects::nonNull)) {
            Related related = answeredApart(sides, calls, states);
            if (related != null) {
                sides = related.sides();
                form = related.form();
            } else if (unread != null) {
                return unread;
            }
        }
        if (form == null) {
            switch (sides.get(0).minus(sides.get(1))) {
                case ExactAnswer.Held<LinearForm<Quantity>>(LinearForm<Quantity> held) ->
                        form = held;
                case ExactAnswer.Unheld<LinearForm<Quantity>>(UnheldNumber why) -> {
                    return new Derivation.Stopped(new WhyUnread.ANumberNotHeld(why), false);
                }
            }
        }
        if (form.coefs().isEmpty()) {
            return new Derivation.ACutThatCutsNothing(states.holds(form.constant().signum()),
                    ofTheInputIn(sides));
        }
        return aRelation(Derivation.ComparisonReading.OVER_BOUND_VALUES, form, states, counting);
    }

    /** The two sides of a comparison read with what an operation answers, and the form they come
     *  to. */
    private record Related(List<LinearForm<Quantity>> sides, LinearForm<Quantity> form) {}

    /**
     * The sides of a comparison with each of {@code calls} read as what its operation answers, where
     * they come to one value against another made of positions apart
     * ({@link #relatesPositionsApart}) or to one value on both — or null where they do not.
     *
     * <p>{@code asRead} is what each side was read as, null where the reading stopped in it, and
     * {@code calls} the call each may be read as instead, null where there is none.
     *
     * <p>Not where {@code states} draws a line. Two values that count to a number held in order
     * are a line on their difference, as {@code x < y} is, and a row at a point of it needs a value
     * of each side there — which nothing here writes for what an operation answers, so the
     * arithmetic says where it stopped. Two values being one, or not, draws no line whatever they
     * count to, and two values that count to nothing draw none however they are held.
     *
     * <p>Asked once both sides were read, so nothing of the comparison is read after what this
     * meets reading the arguments. Those are read beside what the sides met, so an argument naming
     * another element of a container already read of is refused there, as it is in any reading of
     * the two.
     */
    private Related answeredApart(List<LinearForm<Quantity>> asRead, List<Denotation> calls,
                                  Rel states) {
        if (states != Rel.EQ && states != Rel.NE && calls.stream().anyMatch(call -> call != null
                && Carrier.ofValue(call.value().type(), read.rules().declarations())
                        instanceof Carrier carrier && carrier.counts())) {
            return null;
        }
        List<LinearForm<Quantity>> sides = new ArrayList<>();
        boolean answered = false;
        for (int i = 0; i < asRead.size(); i++) {
            Quantity.WhatAnOperationAnswers answers =
                    calls.get(i) == null ? null : whatAnOperationAnswers(calls.get(i));
            if (answers == null && asRead.get(i) == null) {
                return null;
            }
            sides.add(answers != null ? LinearForm.atom(answers) : asRead.get(i));
            answered |= answers != null;
        }
        LinearForm<Quantity> form = sides.get(0).minus(sides.get(1)).orNull();
        return !answered || form == null
                || !(form.coefs().isEmpty() || relatesPositionsApart(form))
                ? null : new Related(sides, form);
    }

    /** The one quantity {@code form} is, weighed by one and moved by nothing — or null where it
     *  is anything else. */
    private static Quantity soleQuantity(LinearForm<Quantity> form) {
        return form.constant().signum() == 0 && form.coefs().size() == 1
                && ExactRatio.ONE.equals(form.coefs().values().iterator().next())
                ? form.coefs().keySet().iterator().next() : null;
    }

    /** Whether {@code form} is a name for a value whose making the reading stopped at, and
     *  nothing besides. */
    private static boolean madeOfWhereItStopped(LinearForm<Quantity> form) {
        return soleQuantity(form) instanceof Quantity.OfABinding bound && bound.madeOf().isPresent();
    }

    /** Where {@code side} stands, where that is the application of an operation of the library to
     *  something — or null where it is not. */
    private Denotation callOf(Denotation side) {
        Denotation stands = side.at().standing(side.value(), read.rules().symbols(),
                read.rules().newtypes());
        return AnOperationApplied.of(Core.withoutStanding(stands.value()))
                instanceof AnOperationApplied applied
                && applied.operation() instanceof ValueName.Stdlib && !applied.args().isEmpty()
                ? stands : null;
    }

    /**
     * What the operation applied at {@code call} answers of values of the input, where it says
     * nothing of its answer as a number of them — or null where it does.
     *
     * <p>An operation that takes a number of its argument, or is defined by cases, is read as that
     * number or on each case, and is none of these. Every argument has to be one value of the
     * input, or another such answer: an argument that comes to anything else — a constant, a sum,
     * what a dependency answered — leaves the call unread.
     */
    private Quantity.WhatAnOperationAnswers whatAnOperationAnswers(Denotation call) {
        AnOperationApplied applied = AnOperationApplied.of(Core.withoutStanding(call.value()));
        ValueName.Stdlib operation = (ValueName.Stdlib) applied.operation();
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        if (facts.takenAs(operation) != null || !facts.isDefinedByCases(operation).isEmpty()) {
            return null;
        }
        List<Quantity> of = new ArrayList<>();
        for (Core argument : applied.args()) {
            Denotation given = new Denotation(argument, call.at());
            Quantity one = AffineForms.outcome(argument, call.at(), quantities())
                    instanceof AffineForms.Outcome.Composed<Quantity, InputReads>(
                            LinearForm<Quantity> form)
                    && soleQuantity(form) instanceof DecisionAtom.OfTheInput input ? input
                    : callOf(given) instanceof Denotation inner ? whatAnOperationAnswers(inner)
                    : null;
            if (one == null) {
                return null;
            }
            of.add(one);
        }
        return new Quantity.WhatAnOperationAnswers(operation, of);
    }

    /**
     * Whether {@code form} weighs one value against another and nothing else, each a number of the
     * input or what an operation answers of the input, the two made of positions apart.
     *
     * <p>{@code d == String.lowercase(s)} relates {@code d} to {@code s} as {@code d == s} does:
     * whatever {@code s} holds, some {@code d} meets it and some does not. Under {@code
     * String.lowercase(s) == String.uppercase(s)} both values are made of {@code s}, and what holds
     * there is which values {@code s} holds — a division of {@code s} this does not read. A position
     * under the other is the same position for this: a field of {@code s} is a part of what
     * {@code s} holds.
     */
    private static boolean relatesPositionsApart(LinearForm<Quantity> form) {
        if (form.constant().signum() != 0 || form.coefs().size() != 2) {
            return false;
        }
        List<List<TermPath>> sides = new ArrayList<>();
        ExactRatio weighed = null;
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            List<NumericTerm> terms = switch (each.getKey()) {
                case DecisionAtom.OfTheInput(NumericTerm term) -> List.of(term);
                case Quantity.WhatAnOperationAnswers answers -> answers.positionsItIsMadeOf();
                default -> null;
            };
            if (terms == null) {
                return false;
            }
            sides.add(terms.stream().flatMap(term -> term.placesReadOff().stream()).toList());
            if (weighed == null) {
                weighed = each.getValue();
                continue;
            }
            ExactRatio cancelled = weighed.plus(each.getValue()).orNull();
            if (cancelled == null || cancelled.signum() != 0) {
                return false;
            }
        }
        for (TermPath p : sides.get(0)) {
            for (TermPath q : sides.get(1)) {
                if (p.isAtOrUnder(q) || q.isAtOrUnder(p)) {
                    return false;
                }
            }
        }
        return true;
    }

    /** {@code form states 0}, read by {@code by}, written the one way every writing of a relation
     *  comes to ({@link Relation.OneWay}). */
    private static Derivation aRelation(Derivation.ComparisonReading by, LinearForm<Quantity> form,
                                        Rel states) {
        return aRelation(by, form, states, Map.of());
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
        Relation.Affine relation = new Relation.Affine(one.form(), one.proposition());
        if (pastTheReadings(relation)) {
            return pastTheReadings(false);
        }
        List<Derivation.AComparisonRead.Counted> named = new ArrayList<>();
        read.forEach((count, how) -> {
            if (one.form().coefs().containsKey(count)) {
                named.add(how);
            }
        });
        return new Derivation.AComparisonRead(by, relation, one.holds(), named,
                READINGS.maximum());
    }

    /**
     * Whether {@code relation} is a count of statements about values written out that is written
     * out as more choices of which of them hold than one condition is read in — which a comparison
     * a reading concludes is never made as ({@link Derivation.AComparisonRead}).
     */
    private static boolean pastTheReadings(Relation relation) {
        return Derivation.AComparisonRead.pastTheChoicesRead(relation, READINGS.maximum());
    }

    /** A comparison stopped at for being {@link #pastTheReadings}. */
    private static Derivation pastTheReadings(boolean fixed) {
        return new Derivation.Stopped(new WhyUnread.MoreReadingsThanAreMade(), fixed);
    }

    /** The block a closure is, read where {@code container} stands. */
    private Function<Core, Core.Block> blocksAt(Denotation container) {
        return closure -> Core.withoutStanding(container.at().standing(closure,
                read.rules().symbols(), read.rules().newtypes()).value())
                instanceof Core.Block block ? block : null;
    }

    /**
     * The value filed under the key of an entry, where {@code node} is the value a walk hands its
     * closure for each entry of a map built by filing a counter under the key of each element of a
     * list ({@link KeyedAccumulation}) — or null where it is no such value.
     *
     * <p>How often the key occurs among the elements, shifted and scaled by what the fold starts
     * the counter at and adds to it: the first element of a key files {@code first} and each
     * further one adds {@code step}, so the value is {@code first + step * (occurrences - 1)}. The
     * key of an element is one number of it, and the elements' own is the number the entry is
     * about.
     */
    private LinearForm<Quantity> valueOfAnEntry(Core node, InputReads at) {
        Core container = at.containerOfTheElement(node);
        if (container == null) {
            return null;
        }
        Denotation whole = at.standing(container, read.rules().symbols(), read.rules().newtypes());
        KeyedAccumulation filed = KeyedAccumulation.of(whole.value(), blocksAt(whole));
        if (filed == null) {
            return null;
        }
        Denotation walked = holdingEachAsOften(whole.at().standing(filed.walked(),
                read.rules().symbols(), read.rules().newtypes()));
        Denotation key = whole.at().standing(filed.key(), read.rules().symbols(),
                read.rules().newtypes());
        if (!(walked.at().pathOf(walked.value(), read.rules().newtypes())
                instanceof PathResolution.At(TermPath held))
                || !(whole.at().pathOf(key.value(), read.rules().newtypes())
                instanceof PathResolution.At(TermPath place))) {
            return null;
        }
        NumericTerm.Multiplicity occurrences = NumericTerm.Multiplicity.of(held, place);
        if (occurrences == null) {
            return null;
        }
        // Which values are the same is the order the key stands on, so a key on none is a key
        // nothing here can count: it is left unread rather than read as a number nothing reads.
        TermOrders orders = read.quantities().ordersOf(occurrences);
        if (orders == null || orders.observed() == null) {
            return null;
        }
        if (filed.step().signum() == 0) {
            return LinearForm.constant(filed.first());
        }
        return filed.first().plus(filed.step().negated())
                instanceof ExactAnswer.Held<ExactRatio>(ExactRatio constant)
                ? new LinearForm<>(constant, Map.of(
                        new DecisionAtom.OfTheInput(occurrences), filed.step()))
                : null;
    }

    /**
     * The seed and the total of what each element adds, where {@code node} is a walk from a seed
     * whose step only adds to the answer so far ({@link InputNumber#ofAWalkAdding}) — or null where
     * it is not.
     */
    private LinearForm<Quantity> seedPlusWhatEachElementAdds(Core node, InputReads at) {
        Core stands = Core.withoutStanding(node);
        if (!(stands instanceof Core.PreservedCall) && !(stands instanceof Core.Read)) {
            return null;
        }
        Denotation walk = at.standing(node, read.rules().symbols(), read.rules().newtypes());
        InputNumber.SeedAndTotal added = InputNumber.ofAWalkAdding(walk.value(), read.domain(),
                walk.at(), read.rules(), blocksAt(walk));
        return added == null ? null : new LinearForm<>(added.seed(),
                Map.of(new DecisionAtom.OfTheInput(added.total()), ExactRatio.ONE));
    }

    /**
     * What {@code container} holds, beneath the operations that only put its elements in another
     * order or answer each of them as it is: the same values, each as often as {@code container}
     * holds it, which is what a count of them is a count of.
     */
    private Denotation holdingEachAsOften(Denotation container) {
        Denotation at = container;
        while (Core.withoutStanding(at.value()) instanceof Core.PreservedCall call) {
            ValueName operation = call.declared().operation();
            BuiltFrom<DeclaredArgument> built =
                    DefaultBoundOperationFacts.get().buildsItsResultFrom(operation);
            DeclaredArgument from = built == null ? null : built.permutesTheElementsOf();
            if (from == null) {
                from = AnIdentityMap.of(operation, call.args(), blocksAt(at));
            }
            if (from == null) {
                break;
            }
            at = at.at().standing(call.args().get(from.position()), read.rules().symbols(),
                    read.rules().newtypes());
        }
        return at;
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
                LinearForm<Quantity> filedUnder = valueOfAnEntry(node, at);
                if (filedUnder != null) {
                    return filedUnder;
                }
                LinearForm<Quantity> added = seedPlusWhatEachElementAdds(node, at);
                if (added != null) {
                    return added;
                }
                NumericTerm term = InputNumber.of(node, read.domain(), at, read.rules(),
                        elementsMet);
                if (term != null) {
                    return LinearForm.atom(new DecisionAtom.OfTheInput(term));
                }
                // A name for another element of a container the comparison is already read of is
                // no number of the input, and what it is made of is not followed further.
                if (elementsMet.crowded()) {
                    return null;
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
                DecisionAtom takenOfAnAnswer = subjects.takenOfAnAnswer(node, at);
                if (takenOfAnAnswer != null) {
                    return LinearForm.atom(takenOfAnAnswer);
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
                    case ReadMeaning.Element _, ReadMeaning.OneOf _, ReadMeaning.NoneHeld _,
                         ReadMeaning.MoreThanAreWrittenOut _, ReadMeaning.Position _ -> null;
                    // A name given a choice between values holds whichever arm was taken, which
                    // is a number for each case and not one the body bound.
                    case ReadMeaning.Through(Denotation denotes)
                            when Choice.of(underItsAccesses(denotes).value()) != null -> null;
                    // And so does one given a value worked out from such a choice, or from what a
                    // behavior's call answers: the reading reads it on each arm, or in the body.
                    case ReadMeaning.Through _ when inside != null && aWayInAt(inside) != null ->
                            null;
                    // A name for one value the source wrote out stands for that value, which no
                    // binding of the body works out: it is no atom of its own, as the value written
                    // where the name is is none. Where the reading of it stopped is still the stop
                    // the walk reports, at the name. A name for one of several written values is
                    // not one value, and stays a name.
                    case ReadMeaning.Through _ when at.writtenOutAsOneValue(name,
                            read.rules().symbols(), read.rules().newtypes()) -> null;
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
            public ValueStanding.ReadThrough<InputReads> readThrough(Core.Read name, InputReads at) {
                // A name given what a dependency answered is read through to the call, which is
                // the evaluation it names ({@link InputReads#answerAt}): the answer a row stands in
                // and a reader walking the tree relates by that evaluation.
                return NameAnswers.denoting(name, at, read.rules().symbols(),
                        read.rules().newtypes());
            }

            @Override
            public List<ValueStanding.ReadThrough<InputReads>> alternativesOf(Core.Read name,
                                                                           InputReads at) {
                return NameAnswers.alternativesOf(name, at, read.rules().symbols(),
                        read.rules().newtypes(), subjects.kept());
            }

            @Override
            public ValueStanding.ReadThrough<InputReads> taken(Core node, InputReads at) {
                return NameAnswers.taken(node, at);
            }

            @Override
            public LinearForm<Core> takenAsAForm(Core node, InputReads at) {
                return NameAnswers.takenAsAForm(node, at);
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
     * Whether two values, each standing as a case written with nothing in it or each as a string
     * written out, are the same — or null where the comparison is no such one.
     *
     * <p>Neither side is a place a row writes at, so there is nothing a line could be drawn on: what
     * it states is the same on every row, and it is what the two values are. {@code Alice == Alice}
     * holds and {@code Alice == Bob} does not, which a filter handed the values written out asks
     * of each element it keeps; and {@code "b" == "a"} does not, which a choice of strings read in
     * each of its cases asks of the case taken ({@link #throughWhatItStopsAt}).
     */
    private Derivation ofTwoValuesWrittenOut(StatedComparison stated, InputReads reads) {
        Rel rel = stated.claim().statedRelation();
        if (rel != Rel.EQ && rel != Rel.NE) {
            return null;
        }
        Object left = valueWrittenAt(stated.left(), reads);
        Object right = left == null ? null : valueWrittenAt(stated.right(), reads);
        // Two of one kind: a case and a string are not compared, and are no answer here.
        return right == null || left.getClass() != right.getClass() ? null
                : new Derivation.WrittenOut(left.equals(right) == (rel == Rel.EQ));
    }

    /** The case {@code side} stands as, where it stands as one written with nothing in it, or the
     *  string, where it stands as one written out — or null. */
    private Object valueWrittenAt(Core side, InputReads reads) {
        return switch (Core.withoutStanding(reads.standing(side, read.rules().symbols(),
                read.rules().newtypes()).value())) {
            case Core.UnitValue unit -> unit.data();
            case Core.Str text -> text.value();
            default -> null;
        };
    }

    /**
     * The subject a row controls that {@code e} is the truth of: a position, or what a dependency
     * answered — or null where it is neither.
     */
    private DecisionSubject truthAt(Core e, InputReads reads) {
        TermPath position = InputTruth.positionOf(e, reads, read.rules().newtypes());
        return position != null ? new DecisionSubject.AnInput(position) : answerAt(e, reads);
    }

    /** The subject a row controls that {@code e} stands for: a position the input is written at, or
     *  what a dependency answered — or null where it is neither. */
    private DecisionSubject subjectOf(Core e, InputReads reads) {
        return reads.pathOf(e, read.rules().newtypes()) instanceof PathResolution.At(TermPath at)
                ? new DecisionSubject.AnInput(at) : answerAt(e, reads);
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
                        asQuantities(DecisionAtom.ofTheInput(against)), states);
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
                states == proposition, READINGS.maximum());
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
                    new Derivation.AnOrderOfItsArguments(callOfAnOrder(operation, ordered),
                            ordered.sign(), firstThatReadsIt(
                            rulesFor(ordered.arguments(), null, fixed, ordered.at())));
            case TheSignOfAnOrder.Read.Settled<InputReads> settled
                    when settled.operation() instanceof ValueName.Stdlib ->
                    new Derivation.ASignItsBoundsSettle(settled.sign());
            // An order the library declares is of one of its own operations.
            case TheSignOfAnOrder.Read.OfTheArguments<InputReads> _,
                 TheSignOfAnOrder.Read.Settled<InputReads> _ -> null;
        };
    }

    /**
     * The call of {@code operation} an order of its arguments is read of, with where its greater
     * and its lesser argument stand: the two sides of what the comparison states of them.
     */
    private Derivation.TheCall callOfAnOrder(
            ValueName.Stdlib operation, TheSignOfAnOrder.Read.OfTheArguments<InputReads> ordered) {
        List<DeclaredArgument> arguments = TheSignOfAnOrder.orderedArguments(operation);
        List<Core> terms = List.of(ordered.arguments().left(), ordered.arguments().right());
        Map<DeclaredArgument, TermPath> standingAt = new HashMap<>();
        for (int i = 0; i < arguments.size(); i++) {
            if (ordered.at().pathOf(terms.get(i), read.rules().newtypes())
                    instanceof PathResolution.At(TermPath at)) {
                standingAt.put(arguments.get(i), at);
            }
        }
        return new Derivation.TheCall(operation, standingAt);
    }

    /**
     * A comparison whose arithmetic stops at a value a reading can go into, read through it — or
     * null where its arithmetic stops at none, or goes through.
     *
     * <p>Two values are gone into. One chosen by cases is read as the choice: in each case, the same
     * comparison read again with the choice standing for what that case answers. Wherever the choice
     * stands in it — added to a number, under a field taken off what each case builds, as the
     * argument of an operation — the comparison holds exactly where it holds of the answer of the
     * case taken, which is {@link #ofAChoice}'s rule for a choice standing anywhere and not only as
     * a whole side. And a call of a behavior no row stands in is read as its body, with the
     * parameters standing for what the call handed ({@link Derivation.ABehaviorsBody}). Each reading
     * is every rule for a comparison again, so a case comes out as a cut on the input where its
     * answer is one.
     *
     * <p>A value is gone into once: read again with it taken, the arithmetic goes through it, and
     * where it stops next is another such value or none at all.
     */
    private Derivation throughWhatItStopsAt(StatedComparison stated, Denotation at, boolean fixed,
                                            InputReads reads) {
        Inside inside = aWayIn(List.of(new Denotation(stated.left(), reads),
                new Denotation(stated.right(), reads)));
        return inside == null ? null : goingIn(inside, reads, at, fixed,
                taking -> comparison(stated, at, fixed, taking.apply(reads)));
    }

    /** A value the arithmetic of a number stopped at, that a reading can go into. */
    private sealed interface Inside {

        /** A value chosen by cases, standing as {@code chosen}. */
        record AChoice(Denotation chosen) implements Inside {}

        /** A call of {@code behavior}, whose body a reading enters as {@code body}. */
        record ACall(Core call, ValueName.Behavior behavior, Denotation body) implements Inside {}

        /**
         * A name standing for one of the values a container was written with, read where no
         * application hands it one: {@code values} are what it can be handed.
         */
        record OneOfTheValues(Core.Read name, List<Denotation> values) implements Inside {}

        /**
         * A call of an operation the library defines in {@code cases} that are no choice between
         * the values it was given — arithmetic over them, reached by how they stand against a
         * constant — read where the call stands, {@code at}.
         */
        record ACallDefinedByCases(Core call, ValueName.Stdlib operation,
                                   List<Choice.ADefinitionCase> cases, InputReads at)
                implements Inside {}
    }

    /**
     * {@code again} read through {@code inside}, handed what puts a reading there
     * ({@link InputReads#taking}): once for each arm of a choice, as the choice, each arm where a
     * run takes it; once in the body of a behavior a call names.
     *
     * @param reads where the reading being split stands, which counts the readings it is one of
     * @param at    where what is read again is a part of a larger condition, or null
     * @param fixed whether its answer is the same on every run
     */
    private Derivation goingIn(Inside inside, InputReads reads, Denotation at, boolean fixed,
                               Function<UnaryOperator<InputReads>, Derivation> again) {
        return switch (inside) {
            case Inside.AChoice(Denotation chosen) -> {
                int arms = Choice.of(Core.withoutStanding(chosen.value())).arms().size();
                if (reads.readings() * arms > READINGS.maximum()) {
                    yield partOf(at, new Derivation.Stopped(
                            new WhyUnread.MoreReadingsThanAreMade(), fixed));
                }
                Core choice = chosen.value();
                yield new Derivation.AComparisonOfAChoice(byItsCases(chosen, at,
                        arm -> again.apply(on -> on.taking(choice, arm, arms))));
            }
            case Inside.ACall(Core call, ValueName.Behavior behavior, Denotation body) ->
                    new Derivation.ABehaviorsBody(behavior,
                            again.apply(on -> on.taking(call, body, 1)));
            case Inside.OneOfTheValues(Core.Read name, List<Denotation> values) -> {
                if (reads.readings() * values.size() > READINGS.maximum()) {
                    yield partOf(at, new Derivation.Stopped(
                            new WhyUnread.MoreReadingsThanAreMade(), fixed));
                }
                List<Derivation> each = new ArrayList<>();
                for (Denotation value : values) {
                    each.add(again.apply(on -> on.handing(name.binding(), value,
                            read.rules().newtypes())));
                }
                yield new Derivation.OnEachValueWrittenOut(each);
            }
            // Once for each case, with the call standing for the arithmetic the case answers, where
            // the arguments stand as the case says and as none before it does — which is what the
            // library proved its body answers ({@link Choice#casesOf}).
            case Inside.ACallDefinedByCases(Core call, ValueName.Stdlib operation,
                                            List<Choice.ADefinitionCase> cases, InputReads where) -> {
                if (reads.readings() * cases.size() > READINGS.maximum()) {
                    yield partOf(at, new Derivation.Stopped(
                            new WhyUnread.MoreReadingsThanAreMade(), fixed));
                }
                List<Derivation.MatchArms.Arm> each = new ArrayList<>();
                for (Choice.ADefinitionCase one : cases) {
                    each.add(new Derivation.MatchArms.Arm(reachedIn(one, where),
                            again.apply(on -> on.takingAForm(call, one.answers(),
                                    cases.size()))));
                }
                yield new Derivation.AnOperationsCases(operation, each);
            }
        };
    }

    /**
     * The values a call was given standing as {@code one}, a case of the definition the library
     * writes its operation in, says they do for it to be reached — each relation read as the
     * arithmetic over those values it is, where the call stands.
     */
    private Derivation reachedIn(Choice.ADefinitionCase one, InputReads where) {
        Derivation reached = null;
        for (Choice.FormsStand stands : one.given()) {
            Derivation relation = overTheValues(stands, where);
            reached = reached == null ? relation
                    : new Derivation.Joined(ConditionJoin.BOTH, reached, relation);
        }
        if (reached == null) {
            // A case reached whatever the arguments are is no case of a choice, and the cases after
            // it would never be reached; the library writes none.
            throw new IllegalStateException("a case of a library operation is reached by no"
                    + " standing of its arguments: " + one);
        }
        return reached;
    }

    /** {@code stands}, over the numbers the values a call was given read as where it stands. */
    private Derivation overTheValues(Choice.FormsStand stands, InputReads where) {
        LinearForm<Core> apart;
        switch (stands.left().minus(stands.right())) {
            case ExactAnswer.Held<LinearForm<Core>>(var held) -> apart = held;
            case ExactAnswer.Unheld<LinearForm<Core>>(UnheldNumber why) -> {
                return new Derivation.Stopped(new WhyUnread.ANumberNotHeld(why), false);
            }
        }
        LinearForm<Quantity> form = LinearForm.constant(apart.constant());
        for (Map.Entry<Core, ExactRatio> each : apart.coefs().entrySet()) {
            switch (AffineForms.outcome(each.getKey(), where, quantities())) {
                case AffineForms.Outcome.Composed<Quantity, InputReads>(var argument) -> {
                    LinearForm<Quantity> before = form;
                    switch (argument.times(each.getValue()).flatMap(before::plus)) {
                        case ExactAnswer.Held<LinearForm<Quantity>>(var held) -> form = held;
                        case ExactAnswer.Unheld<LinearForm<Quantity>>(UnheldNumber why) -> {
                            return new Derivation.Stopped(new WhyUnread.ANumberNotHeld(why),
                                    false);
                        }
                    }
                }
                case AffineForms.Outcome.StoppedAt<Quantity, InputReads> stopped -> {
                    return new Derivation.Stopped(noFormOf(stopped), false);
                }
            }
        }
        if (form.coefs().isEmpty()) {
            return new Derivation.ACutThatCutsNothing(
                    stands.rel().holds(form.constant().signum()), Set.of());
        }
        return aRelation(Derivation.ComparisonReading.OVER_BOUND_VALUES, form, stands.rel());
    }

    /**
     * The first value the arithmetic of one of {@code numbers} stops at that a reading can go into
     * and has not gone into yet — or null where it stops at none.
     */
    private Inside aWayIn(List<Denotation> numbers) {
        for (Denotation number : numbers) {
            if (AffineForms.outcome(number.value(), number.at(), quantities())
                    instanceof AffineForms.Outcome.StoppedAt<Quantity, InputReads> stopped) {
                Inside found = aWayInAt(stopped);
                boolean goneInto = switch (found) {
                    case null -> true;
                    case Inside.AChoice(Denotation chosen) ->
                            number.at().taken(chosen.value()) != null;
                    case Inside.ACall(Core call, var _, var _) -> number.at().taken(call) != null;
                    case Inside.ACallDefinedByCases(Core call, var _, var _, var _) ->
                            number.at().isTaken(call);
                    // A name an application handed a value is that one value, and stops nothing.
                    // Met again as several, it was reached through a value handed another name and
                    // read where that value was written, which no application handed it: handed
                    // here once more, it would be met there again without end.
                    case Inside.OneOfTheValues(Core.Read name, var _) ->
                            number.at().hands(name.binding());
                };
                if (!goneInto) {
                    return found;
                }
            }
        }
        return null;
    }

    /**
     * The value the arithmetic stopped at, where a reading can go into it — through an argument of
     * a call it reads the form of, under the accesses taken off it, and as what an operation it has
     * no form for was handed — or null where what it stopped at is no such value.
     */
    private Inside aWayInAt(AffineForms.Outcome.StoppedAt<Quantity, InputReads> stopped) {
        return switch (stopped.why()) {
            case AffineForms.Halt.AnArgumentStopped<Quantity, InputReads>(var argument) ->
                    aWayInAt(argument);
            case AffineForms.Halt.NoRule<Quantity, InputReads> _,
                 AffineForms.Halt.ValuesDisagree<Quantity, InputReads> _ ->
                    aWayInto(underItsAccesses(new Denotation(stopped.node(), stopped.at())),
                            new HashSet<>());
            case AffineForms.Halt.NotLinear<Quantity, InputReads> _,
                 AffineForms.Halt.NoNumberOnARun<Quantity, InputReads> _,
                 AffineForms.Halt.NotHeld<Quantity, InputReads> _ -> null;
        };
    }

    /**
     * The first value a reading can go into at {@code value} or inside it — what it is chosen by
     * cases, a behavior's call, a name standing for one of several values written out, or, failing
     * those, one of them inside what an operation was handed or an operator works out — or null
     * where there is none.
     *
     * <p>Wherever inside: a size of a container one of whose parts is chosen by cases is the size
     * of what the case taken answers, however deep the choice stands, and the reading reads it on
     * each.
     *
     * @param met the bindings already read through on the way here
     */
    private Inside aWayInto(Denotation value, Set<BindingId> met) {
        Denotation chosen = chosenAt(value);
        if (chosen != null) {
            return new Inside.AChoice(chosen);
        }
        Inside.ACall called = intoACall(value);
        if (called != null) {
            return called;
        }
        Denotation stands = value.at().standing(value.value(), read.rules().symbols(),
                read.rules().newtypes());
        Core e = Core.withoutStanding(stands.value());
        // Every value it may be handed on some row: what is read on each is a statement of an
        // application it may be handed ({@link Proposition.OnAnApplication}), and one dropped on
        // every row is handed on none. Where none is left there is no value to go into.
        if (e instanceof Core.Read name && met.add(name.binding())
                && stands.at().meaningOf(name, read.rules().symbols(), read.rules().newtypes())
                        instanceof ReadMeaning.OneOf one) {
            List<Denotation> values = one.valuesWhere(KeptTruths.readIn(read));
            return values.isEmpty() ? null : new Inside.OneOfTheValues(name, values);
        }
        // A closure's body is read where it is applied, and is no part of this value.
        if (e instanceof Core.Block) {
            return null;
        }
        Inside[] found = {null};
        Core.forEachChild(e, child -> {
            if (found[0] == null) {
                found[0] = aWayInto(new Denotation(child, stands.at()), met);
            }
        });
        // A call defined by cases is gone into once what it was handed reads as one number on
        // each reading, since its cases are relations over those numbers.
        return found[0] != null ? found[0] : definedByCases(e, stands.at());
    }

    /**
     * {@code e}, where it is a call of an operation the library defines in cases that are no choice
     * between the values it was given ({@link Inside.ACallDefinedByCases}), or null.
     *
     * <p>Not one whose cases are such a choice: those are read as the choice it is
     * ({@link #chosenAt}), and read here as well they would be read twice.
     */
    private Inside.ACallDefinedByCases definedByCases(Core e, InputReads at) {
        if (!(Core.withoutStanding(e) instanceof Core.PreservedCall call)
                || Choice.of(call) != null
                || !(AnOperationApplied.of(call) instanceof AnOperationApplied applied
                        && applied.operation() instanceof ValueName.Stdlib operation)) {
            return null;
        }
        List<Choice.ADefinitionCase> cases = Choice.casesOf(call);
        return cases.isEmpty() ? null
                : new Inside.ACallDefinedByCases(call, operation, cases, at);
    }

    /**
     * {@code value}, where it is a call of a behavior no row stands in, entered: the behavior's body
     * read with its parameters standing for what the call handed ({@link InputReads#calling}) — or
     * null where it is no such call, or the body is not read there: it has none, or it is entered
     * already on the way here.
     */
    private Inside.ACall intoACall(Denotation value) {
        Core e = Core.withoutStanding(value.value());
        if (!(AnOperationApplied.of(e) instanceof AnOperationApplied applied
                && applied.operation() instanceof ValueName.Behavior behavior)
                || value.at().standsIn(behavior)) {
            return null;
        }
        Optional<CalledBody> body = read.rules().declarations().answers().bodyOf(behavior);
        InputReads inside = body.isEmpty() ? null : value.at().calling(behavior, body.get(),
                applied.args(), read.rules().newtypes());
        return inside == null ? null
                : new Inside.ACall(e, behavior, new Denotation(body.get().body(), inside));
    }

    /**
     * How {@code e}, a call of a behavior no row stands in, answers {@code asked}, read off the
     * behavior's body where the call stands — or null where it is no such call, or the body is not
     * read there ({@link #intoACall}).
     */
    private Derivation inTheCalledBody(Core e, Asked asked, InputReads reads) {
        Inside.ACall called = intoACall(new Denotation(e, reads));
        return called == null ? null : new Derivation.ABehaviorsBody(called.behavior(),
                observe(called.body().value(), asked, called.body().at()));
    }

    /**
     * How what a walk from a seed ends with coming out on {@code aspect} was read, by induction
     * over the elements it walks ({@link Derivation.AcrossAWalk}) — or null where {@code e} is no
     * such walk, the elements it walks stand at no subject, or its step does not keep what it
     * carried on that side.
     *
     * <p>The step is read once, with what it was carried standing as itself, and concluded with
     * that supposed to have come out each way. Where every part of both was read and one of them
     * comes out as what was carried whatever those parts are, the step keeps that side, and the
     * other is what an element has to meet. Read once, a walk inside the step is read once for it
     * however deep the walks go.
     */
    private Derivation acrossAWalk(Core e, AnswerAspect aspect, InputReads reads) {
        SeededWalk walk = SeededWalk.of(e, blocksAt(new Denotation(e, reads)));
        DecisionSubject container = walk == null ? null : subjectOf(walk.container(), reads);
        if (container == null || !quantifying.add(container)) {
            return null;
        }
        ACarriedValue value = ACarriedValue.made();
        Derivation step;
        try {
            step = stepCarrying(walk, aspect, value, reads);
        } finally {
            quantifying.remove(container);
        }
        return closed(observe(walk.seed(), aspect, reads), container, walk.container(), step,
                value, e, reads);
    }

    /**
     * How what a recursion over a list ({@link RecursionOverAList}) answers coming out on
     * {@code aspect} was read, by induction over the elements it walks, as a walk's end is
     * ({@link #acrossAWalk}) — or null where {@code e} calls no such recursion, the list it is
     * handed stands at no position, or its step does not keep what the rest answered on that side.
     *
     * <p>The step is the arm taken where the list holds something, read with its head standing for
     * an element of the list and its calls of itself standing for what the rest answered; the end is
     * the arm taken where it holds nothing, which is read only where it comes out the same whatever
     * the row is — read on the list as handed, it would be read of a list that holds something.
     */
    private Derivation acrossARecursion(Core e, AnswerAspect aspect, InputReads reads) {
        if (!(AnOperationApplied.of(e) instanceof AnOperationApplied(
                ValueName.Helper helper, List<Core> args)) || !recursing.add(helper)) {
            return null;
        }
        try {
            return ofARecursion(helper, args, aspect, e, reads);
        } finally {
            recursing.remove(helper);
        }
    }

    private Derivation ofARecursion(ValueName.Helper helper, List<Core> args, AnswerAspect aspect,
                                    Core e, InputReads reads) {
        ARecursion recursion =
                read.rules().declarations().answers().recursionOf(helper).orElse(null);
        if (recursion == null) {
            return null;
        }
        CalledBody body = recursion.body();
        RecursionOverAList walk = recursion.walk().orElse(null);
        if (walk == null) {
            return recursion.search().map(search -> acrossATree(helper, body, search, args,
                    aspect, e, reads)).orElse(null);
        }
        if (!(reads.pathOf(args.get(walk.walked()), read.rules().newtypes())
                instanceof PathResolution.At(TermPath list))) {
            return null;
        }
        InputReads step = reads.steppingThrough(body, args, walk.element().binding(),
                list.element(), read.rules().newtypes());
        DecisionSubject container = new DecisionSubject.AnInput(list);
        if (step == null || !quantifying.add(container)) {
            return null;
        }
        ACarriedValue rest = ACarriedValue.made();
        Derivation end;
        Derivation stepped;
        try {
            end = observe(walk.none().body(), aspect, step);
            if (!(trying.of(end) instanceof Proposition.Always)) {
                return null;
            }
            stepped = supposing(walk.again(), new Carried(aspect, rest),
                    () -> observe(walk.some().body(), aspect, step));
        } finally {
            quantifying.remove(container);
        }
        Derivation closed = closed(end, container, args.get(walk.walked()), stepped, rest, e,
                reads);
        return closed == null ? null : new Derivation.ARecursionsBody(helper, closed);
    }

    /** What {@code reading} reads, with each of {@code calls} supposed to answer {@code supposed}. */
    private Derivation supposing(List<Core.Call> calls, Supposed supposed,
                                 Supplier<Derivation> reading) {
        for (Core.Call again : calls) {
            recursed.put(again, supposed);
        }
        try {
            return reading.get();
        } finally {
            calls.forEach(recursed::remove);
        }
    }

    /**
     * What a call of a recursion whose body is being read answers on {@code aspect}, as it is
     * supposed to — or null where it is asked on another side, or a call of a search is on no node
     * below the one the search is read from, or below it through a field the search was not read
     * going down.
     */
    private Derivation supposedOf(Core.Call call, Supposed supposed, AnswerAspect aspect,
                                  InputReads reads) {
        return switch (supposed) {
            case Carried carried -> carried.aspect() == aspect
                    ? new Derivation.WhatAWalkCarried(carried.value()) : null;
            case Descending down -> {
                String field = down.aspect() == aspect
                        ? belowOneStep(call.args().get(down.node()), down.from(), reads) : null;
                if (field == null) {
                    yield null;
                }
                down.through().add(field);
                yield new Derivation.WhatAWalkCarried(down.value());
            }
            case Reaching reaching -> {
                String field = reaching.aspect() == aspect
                        ? belowOneStep(call.args().get(reaching.node()), reaching.from(), reads)
                        : null;
                yield field == null || !reaching.through().contains(field) ? null
                        : new Derivation.AReachedNode(reaching.from().then(field).element(),
                                reaching.from(), reaching.through(), reaching.atANode(),
                                reaching.how());
            }
        };
    }

    /**
     * The field of the node at {@code from} whose element {@code node} stands at — or null where it
     * stands at none, so a call handed it is on no node one step below.
     */
    private String belowOneStep(Core node, TermPath from, InputReads reads) {
        if (!(reads.pathOf(node, read.rules().newtypes()) instanceof PathResolution.At(
                TermPath at)) || at.steps().size() != from.steps().size() + 2
                || !(at.steps().get(from.steps().size()) instanceof TermPath.Step.Field(
                        String field))) {
            return null;
        }
        return at.equals(from.then(field).element()) ? field : null;
    }

    /**
     * How what a search from a node ({@link RecursionOverATree}) answers coming out on
     * {@code aspect} was read, by induction over the nodes below it
     * ({@link Derivation.ATreeSearched}) — or null where it is not read so.
     *
     * <p>It is read where the node it is handed stands at a position, every other value it is
     * handed does too and is neither under the node nor holds it, and every call it makes of itself
     * is on an element of a field of the node. The body is read once with those calls standing for
     * one value, concluded with it supposed to have come out the way that leaves the answer to the
     * node — failed, and where that does not close, held — which is what a node has to meet; that
     * has to be read whole and say the same of any node it is moved to ({@link WrittenOfANode}). It
     * is read again with each call standing for the search from its node, and what that says has to
     * be the search one step down whatever its parts are.
     */
    private Derivation acrossATree(ValueName.Helper helper, CalledBody body,
                                   RecursionOverATree search, List<Core> args, AnswerAspect aspect,
                                   Core e, InputReads reads) {
        if (!(reads.pathOf(args.get(search.node()), read.rules().newtypes())
                instanceof PathResolution.At(TermPath node))) {
            return null;
        }
        List<TermPath> staying = new ArrayList<>();
        for (int at = 0; at < args.size(); at++) {
            if (at == search.node()) {
                continue;
            }
            // One under the node or holding it is refused before the body is read.
            if (!(reads.pathOf(args.get(at), read.rules().newtypes())
                    instanceof PathResolution.At(TermPath stays))
                    || !WrittenOfANode.apart(stays, node)) {
                return null;
            }
            staying.add(stays);
        }
        InputReads inside = reads.searching(body, args, read.rules().newtypes());
        if (inside == null) {
            return null;
        }
        ACarriedValue below = ACarriedValue.made();
        Set<String> went = new TreeSet<>();
        Derivation atAnyNode = supposing(search.again(),
                new Descending(aspect, search.node(), node, below, went),
                () -> observe(body.body(), aspect, inside));
        if (went.isEmpty()) {
            return null;
        }
        List<String> through = List.copyOf(went);
        for (ConditionJoin how : List.of(ConditionJoin.EITHER, ConditionJoin.BOTH)) {
            Derivation searched = searched(body, search, node, staying, through,
                    new Derivation.Supposing(atAnyNode, below, how == ConditionJoin.BOTH), how,
                    aspect, e, reads, inside);
            if (searched != null) {
                return new Derivation.ARecursionsBody(helper, searched);
            }
        }
        return null;
    }

    /** {@link #acrossATree}, with the calls supposed to have come out the way {@code how} leaves
     *  the answer to the node, which is {@code atANode}. */
    private Derivation searched(CalledBody body, RecursionOverATree search, TermPath node,
                                List<TermPath> staying, List<String> through, Derivation atANode,
                                ConditionJoin how, AnswerAspect aspect, Core e, InputReads reads,
                                InputReads inside) {
        Proposition stated = trying.of(atANode);
        if (Proposition.leavesSomethingUnread(stated)
                || !WrittenOfANode.movesWithIt(stated, node, staying)) {
            return null;
        }
        Derivation unfolded = supposing(search.again(),
                new Reaching(aspect, search.node(), node, through, atANode, how),
                () -> observe(body.body(), aspect, inside));
        Proposition oneStepDown = trying.of(unfolded);
        if (Proposition.leavesSomethingUnread(oneStepDown) || !Derivation.ATreeSearched
                .unfoldsOnce(oneStepDown, stated, node, through, how)) {
            return null;
        }
        List<Derivation> below = new ArrayList<>();
        for (String field : through) {
            DecisionAtom size = sizeOfSubject(new DecisionSubject.AnInput(node.then(field)), null);
            if (size == null) {
                below = null;
                break;
            }
            below.add(leaf(new Derivation.SizeAboveNought(size),
                    askedAt != null ? askedAt : new Denotation(e, reads)));
        }
        return new Derivation.ATreeSearched(node, through, atANode, Optional.ofNullable(below),
                unfolded, how);
    }

    /**
     * What a walk over {@code container} ends with, from {@code start}, where its step was read
     * with what it was carried standing as {@code value} — or null where the step concluded with
     * that supposed either way keeps it whatever its parts are on neither side, or some part of
     * them was not read.
     *
     * @param walked the expression the container is, whose size is read where some element meeting
     *               the step has the container's holding anything as a part
     */
    private Derivation closed(Derivation start, DecisionSubject container, Core walked,
                              Derivation step, ACarriedValue value, Core e, InputReads reads) {
        Derivation carriedNothing = new Derivation.Supposing(step, value, false);
        Derivation carriedSomething = new Derivation.Supposing(step, value, true);
        Proposition whereNothing = trying.of(carriedNothing);
        Proposition whereSomething = trying.of(carriedSomething);
        if (Proposition.leavesSomethingUnread(whereNothing)
                || Proposition.leavesSomethingUnread(whereSomething)) {
            return null;
        }
        ConditionJoin how;
        Derivation meets;
        Derivation keeps;
        if (TruthTable.holdsWhateverItsPartsAre(whereSomething)) {
            how = ConditionJoin.EITHER;
            meets = carriedNothing;
            keeps = carriedSomething;
        } else if (TruthTable.failsWhateverItsPartsAre(whereNothing)) {
            how = ConditionJoin.BOTH;
            meets = carriedSomething;
            keeps = carriedNothing;
        } else {
            return null;
        }
        boolean holds = how == ConditionJoin.EITHER;
        Proposition element = holds ? trying.of(meets) : trying.of(meets).denied();
        Optional<Derivation> holdsSomething = Optional.empty();
        if (Derivation.SomeElementMeeting.asksWhetherItHoldsAnything(container, element)) {
            DecisionAtom size = sizeOfSubject(container, Core.withoutStanding(walked).type());
            holdsSomething = Optional.of(size != null
                    ? leaf(new Derivation.SizeAboveNought(size),
                            askedAt != null ? askedAt : new Denotation(e, reads))
                    : unread(walked, reads, new WhyUnread.NoMeasureOfItsSize()));
        }
        return new Derivation.AcrossAWalk(start,
                new Derivation.SomeElementMeeting(container, meets, holds, holdsSomething), keeps,
                how);
    }

    /** {@code walk}'s step coming out on {@code aspect}, with what it was carried standing as
     *  {@code value} there. */
    private Derivation stepCarrying(SeededWalk walk, AnswerAspect aspect, ACarriedValue value,
                                    InputReads reads) {
        BindingId accumulator = walk.accumulator().binding();
        Carried outer = carried.put(accumulator, new Carried(aspect, value));
        try {
            return observe(walk.step().body(), aspect, reads);
        } finally {
            if (outer == null) {
                carried.remove(accumulator);
            } else {
                carried.put(accumulator, outer);
            }
        }
    }

    /**
     * A comparison of the year of a date no position holds with a year written out, read as the
     * comparison of that date with where the year begins — or null where it is no such comparison.
     *
     * <p>A year is a run of days, so the years from one on are the dates from the first day of it
     * on, and {@code Date.year(Date.addDays(n, b)) >= 2027} says what
     * {@code Date.addDays(n, b) >= Date("2027-01-01")} does. That comparison is read where the date
     * is a form of the input's own, which is where a year of it has no term of its own: a taking is
     * of a position, or of a position's date moved by a count of days written out
     * ({@link NumericTerm.TakenOf#transformation()}). A date that is either is left to the term
     * that stands for its year, and what is read here is a date moved by a count an input supplies.
     *
     * <p>Equality is the dates of that year, and a difference is the dates outside it. A date the
     * shift takes off the end of the range is no date, and which inputs make it so is not this
     * reading's: the comparison is read over the dates it is about, as
     * {@code Date.addDays(n, b) >= Date("2027-01-01")} is, and a row that would abort there is
     * never a row that reached a line.
     *
     * <p>Only the parts that are runs of days. A month or a day of the month repeats every year,
     * so it is no line on the date.
     */
    private Derivation ofTheYearOfADate(StatedComparison stated, Denotation at, boolean fixed,
                                        InputReads reads) {
        StatedComparison.Numbered<Core.PreservedCall> year =
                stated.at(side -> theYearOfADateNoPositionHolds(side, reads));
        BigDecimal written = year == null ? null
                : StatedComparison.foldedNumber(year.other(), read.rules().symbols());
        if (written == null) {
            return null;
        }
        Core.PreservedCall taking = year.number();
        // A year past either end of the dates is the same one for the comparison, so it is held
        // just past the end and the sum with one below cannot leave the range of a long.
        long below = Year.MIN_VALUE - 2L;
        long above = Year.MAX_VALUE + 2L;
        long from = written.compareTo(BigDecimal.valueOf(below)) <= 0 ? below
                : written.compareTo(BigDecimal.valueOf(above)) >= 0 ? above
                : written.longValue();
        return switch (year.claim().statedRelation()) {
            case GE -> comparedWithTheStartOf(from, Rel.GE, taking, at, fixed, reads);
            case GT -> comparedWithTheStartOf(from + 1, Rel.GE, taking, at, fixed, reads);
            case LE -> comparedWithTheStartOf(from + 1, Rel.LT, taking, at, fixed, reads);
            case LT -> comparedWithTheStartOf(from, Rel.LT, taking, at, fixed, reads);
            case EQ -> new Derivation.Joined(ConditionJoin.BOTH,
                    comparedWithTheStartOf(from, Rel.GE, taking, at, fixed, reads),
                    comparedWithTheStartOf(from + 1, Rel.LT, taking, at, fixed, reads));
            case NE -> new Derivation.Joined(ConditionJoin.EITHER,
                    comparedWithTheStartOf(from, Rel.LT, taking, at, fixed, reads),
                    comparedWithTheStartOf(from + 1, Rel.GE, taking, at, fixed, reads));
        };
    }

    /**
     * A comparison of a count of whole units between two values, read as the comparison of the steps
     * between them it states ({@link WholeUnitsBetween}) — or null where it is no such comparison.
     *
     * <p>The count drops what is left of a unit toward zero, so it is no form of the two values and
     * the walk over arithmetic has nothing to say of it. What it states is exact all the same, and
     * is read here as the difference of the two against the steps it comes to: a count of minutes
     * above five is a difference of six minutes' seconds or more. Equality is the steps between two
     * thresholds, which is a stretch of both signs around nought and not the two values being equal,
     * and a difference is the steps outside it.
     */
    private Derivation ofACountOfWholeUnits(StatedComparison stated, Denotation at, boolean fixed,
                                            InputReads reads) {
        WholeUnitsBetween.Read<InputReads> counted =
                WholeUnitsBetween.read(stated, reads, sides());
        if (counted == null) {
            return null;
        }
        Core to = counted.to();
        Core difference = new Core.Binary(BinOp.SUB, to, counted.from(),
                Core.BinaryReading.AS_THEY_STAND, ConstructOccurrence.unwritten(), Type.INT,
                to.pos());
        return theStatementStands(counted.statement(), difference, at, fixed, counted.at());
    }

    /**
     * A comparison of what a division leaves of a place moved by a number, read as the comparison of
     * what it leaves of the place ({@link RemainderOfAShiftedValue}) — or null where it is no such
     * comparison.
     *
     * <p>What a rule over {@code Int.floorMod(x + 1, 7)} states of {@code x} is exactly what a rule
     * over {@code Int.floorMod(x, 7)} states of it, over the one stretch of remainders or the other.
     * The call is read as it is written when its first argument is the place, which is the number
     * taken of a place, and the moving is peeled off here and nowhere else.
     */
    private Derivation ofAShiftedRemainder(StatedComparison stated, Denotation at, boolean fixed,
                                           InputReads reads) {
        RemainderOfAShiftedValue.Read<InputReads> shifted =
                RemainderOfAShiftedValue.read(stated, reads, sides());
        if (shifted == null) {
            return null;
        }
        return theStatementStands(shifted.statement(), shifted.remainder(), at, fixed,
                shifted.at());
    }

    /**
     * A comparison of what a division by a written number leaves of a form of the input's numbers,
     * read as a comparison of that remainder — or null where it is no such comparison.
     *
     * <p>{@code Int.floorMod(a - d, 7) >= 1} is no line on {@code a} or on {@code d}: the values it
     * holds of come round every seventh of their difference. It is a line on the remainder, which is
     * a number of its own between nought and six, and a row is a pair of values whose difference
     * leaves it ({@link Quantity.RemainderOfADividend}).
     *
     * <p>The dividend is read as any side of a comparison is, so it is the form the arithmetic would
     * make of it anywhere else; and it is read whole, its moving part of its constant. Only whole
     * numbers: a remainder of a form that weighs a number by a fraction is the remainder of what
     * the host cannot hold, and is left unread.
     */
    private Derivation ofARemainderOfAForm(StatedComparison stated, InputReads reads) {
        RemainderOfAShiftedValue.OfAForm<InputReads> over =
                RemainderOfAShiftedValue.readOverAForm(stated, reads, sides());
        if (over == null) {
            return null;
        }
        LinearForm<NumericTerm> dividend = AffineReading.formOf(over.dividend(), over.at(), read);
        if (dividend == null || dividend.coefs().isEmpty() || !isWhole(dividend)) {
            return null;
        }
        return switch (over.statement()) {
            case ConstantComparison.Settled(boolean holds) -> new Derivation.WrittenOut(holds);
            case ConstantComparison.Against(Rel rel, BigInteger against) -> {
                // The constant by the divisor's own remainder, so a dividend moved by a whole turn
                // is the dividend it was before the moving.
                LinearForm<NumericTerm> moved = new LinearForm<>(
                        ExactRatio.of(constantOf(dividend).mod(over.divisor())), dividend.coefs());
                Quantity remainder = new Quantity.RemainderOfADividend(moved, over.divisor());
                LinearForm<Quantity> relation = LinearForm.<Quantity>atom(remainder)
                        .minus(LinearForm.<Quantity>constant(ExactRatio.of(against))).orNull();
                yield relation == null ? null
                        : aRelation(Derivation.ComparisonReading.AS_A_CUT, relation, rel);
            }
            // What the range of a remainder leaves a comparison is one line or a settled answer.
            case ConstantComparison.Both _, ConstantComparison.Either _ -> null;
        };
    }

    /** Whether every number of {@code form}, its constant included, is a whole one. */
    private static boolean isWhole(LinearForm<NumericTerm> form) {
        return form.constant().isWhole()
                && form.coefs().values().stream().allMatch(ExactRatio::isWhole);
    }

    /** The constant of a form every number of which is whole. */
    private static BigInteger constantOf(LinearForm<NumericTerm> form) {
        return ((ExactAnswer.Held<BigInteger>) form.constant().floor()).value();
    }

    /**
     * What {@code statement} says of {@code subject}, read as the comparisons of it that it is.
     *
     * <p>Each comparison is read as any comparison is, so a rule that turns one thing into another
     * hands over the tree of what the other states and nothing of how it is read. A comparison the
     * range of the number settles is the same for every value and has nothing to be written against.
     */
    private Derivation theStatementStands(ConstantComparison statement, Core subject,
                                          Denotation at, boolean fixed, InputReads reads) {
        return switch (statement) {
            case ConstantComparison.Settled(boolean holds) -> new Derivation.WrittenOut(holds);
            case ConstantComparison.Both(var first, var second) ->
                    new Derivation.Joined(ConditionJoin.BOTH,
                            theStatementStands(first, subject, at, fixed, reads),
                            theStatementStands(second, subject, at, fixed, reads));
            case ConstantComparison.Either(var first, var second) ->
                    new Derivation.Joined(ConditionJoin.EITHER,
                            theStatementStands(first, subject, at, fixed, reads),
                            theStatementStands(second, subject, at, fixed, reads));
            case ConstantComparison.Against(Rel rel, BigInteger against) -> comparison(
                    new StatedComparison(ComparisonClaim.stating(rel), subject,
                            new Core.Int(against.longValue(), Type.INT, subject.pos()),
                            Core.BinaryReading.AS_THEY_STAND), at, fixed, reads);
        };
    }

    /** {@code side}, where it is the year of a date that stands at no position. */
    private Core.PreservedCall theYearOfADateNoPositionHolds(Core side, InputReads reads) {
        if (!(Core.withoutStanding(side) instanceof Core.PreservedCall call)
                || !call.operation().equals(ValueName.Stdlib.operation("Date", "year"))
                || call.args().size() != 1) {
            return null;
        }
        Core date = call.args().getFirst();
        return Type.DATE.equals(date.type()) && reads.pathOf(date, read.rules().newtypes())
                instanceof PathResolution.NotAPosition ? call : null;
    }

    /**
     * The date {@code taking} is the year of, compared with the first day of {@code year}: on or
     * after it, or before it.
     *
     * <p>A year no date has is before every date or after every one, so the comparison is the same
     * for all of them and there is no day to write it against.
     */
    private Derivation comparedWithTheStartOf(long year, Rel relation, Core.PreservedCall taking,
                                              Denotation at, boolean fixed, InputReads reads) {
        if (year < Year.MIN_VALUE || year > Year.MAX_VALUE) {
            boolean onOrAfter = year < Year.MIN_VALUE;
            return new Derivation.WrittenOut(relation == Rel.GE ? onOrAfter : !onOrAfter);
        }
        Core start = new Core.Temporal(Type.Prim.DATE, LocalDate.of((int) year, 1, 1).toString(),
                taking.application(), taking.pos());
        return comparison(new StatedComparison(ComparisonClaim.stating(relation),
                taking.args().getFirst(), start, new Core.BinaryReading.AsTheyStand()), at, fixed,
                reads);
    }

    /**
     * A comparison over how many an operation answers, where which number that is turns on how the
     * operation's arguments stand: read in each case of it, as a choice is read in each of its
     * cases — or null where neither side takes such a size.
     */
    private Derivation ofASizeInCases(StatedComparison stated, Denotation at, InputReads reads) {
        Denotation left = new Denotation(stated.left(), reads);
        Denotation right = new Denotation(stated.right(), reads);
        if (measuredByCases(left) == null && measuredByCases(right) == null) {
            return null;
        }
        return new Derivation.AComparisonOfAChoice(
                comparedCase(left, right, stated.claim().statedRelation(), at));
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
        if (byRight != null) {
            return byRight;
        }
        // A choice inside a side rather than the whole of it is split on as well, and a call of a
        // behavior entered, both sides read there ({@link #throughWhatItStopsAt}).
        Inside inside = aWayIn(List.of(left, right));
        if (inside != null) {
            return goingIn(inside, left.at(), at, false, taking -> comparedCase(
                    new Denotation(left.value(), taking.apply(left.at())),
                    new Denotation(right.value(), taking.apply(right.at())), states, at));
        }
        // And how many an operation answers, where which number that is turns on how its
        // arguments stand.
        SizedByCases sized = measuredByCases(left);
        if (sized == null) {
            sized = measuredByCases(right);
        }
        if (sized != null) {
            return inEachCaseOf(sized, at, () -> comparedCase(left, right, states, at));
        }
        return partOf(at, overQuantities(left, right, states));
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
            cases.add(new Derivation.MatchArms.Arm(howTheArgumentsStand(arm, where, at),
                    compared.apply(new Denotation(arm.answers(), where))));
        }
        return new Derivation.AnOperationsCases(operation, cases);
    }

    /**
     * The arguments of a call standing as {@code arm}, one case of the definition the library
     * writes the operation in, says they do for it to be reached — each relation read as the
     * comparison it is, where the call stands.
     */
    private Derivation howTheArgumentsStand(Choice.Arm arm, InputReads where, Denotation at) {
        Derivation reached = null;
        for (Choice.ArgumentRelation stands : relationsDeciding(arm)) {
            Derivation one = comparedCase(new Denotation(stands.left(), where),
                    new Denotation(stands.right(), where), stands.rel(), at);
            reached = reached == null ? one
                    : new Derivation.Joined(ConditionJoin.BOTH, reached, one);
        }
        if (reached == null) {
            // A case reached whatever the arguments are is no case of a choice, and the cases after
            // it would never be reached; the library writes none.
            throw new IllegalStateException("a case of a library operation is reached by no"
                    + " standing of its arguments: " + arm);
        }
        return reached;
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
            public ValueStanding.ReadThrough<InputReads> standing(Core e, InputReads at) {
                Denotation stands = at.standing(e, read.rules().symbols(),
                        read.rules().newtypes());
                return new ValueStanding.ReadThrough<>(stands.value(), stands.at());
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
    private WhyUnread unreadAs(AnOperationApplied applied, AnswerAspect aspect,
                               InputReads reads) {
        if (applied == null) {
            return new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT);
        }
        return switch (applied.operation()) {
            case ValueName.Stdlib operation -> new WhyUnread.NoLawFor(operation, aspect);
            case ValueName.Behavior behavior -> aspect == AnswerAspect.EMPTINESS
                    && reads.standsIn(behavior)
                    ? new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT)
                    : whatABehaviorAnswers(behavior, reads);
            case ValueName.Helper _ -> new WhyUnread.WhatARecursiveHelperAnswers();
            default -> new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT);
        };
    }

    /** A law naming {@code subject}, which the binding of laws refuses: what another operation
     *  answers, and the key an element is filed under, are named in lemmas and nowhere a reader
     *  is handed. */
    private static IllegalStateException namedInNoLaw(LawSubject<DeclaredArgument> subject) {
        return new IllegalStateException("a law names " + subject
                + ", which only a lemma about a library body may name");
    }

    /**
     * Why what {@code behavior} answered was read as nothing.
     *
     * <p>A dependency's answer is the one a row stands in wherever the model writes the call
     * ({@link DecisionSubjects#anAnswer}), so one of them unread is a call no source wrote. Any other
     * behavior's is read off its body where the call stands ({@link #intoACall}), and one that was
     * not is one whose body was entered already on the way here — the behavior reached again while
     * its own answer is being read — or one with no body read: inside a body a call entered, a
     * dependency of that body, whose answer each call names afresh; anywhere, a behavior called with
     * another number of values than it takes.
     */
    private WhyUnread whatABehaviorAnswers(ValueName.Behavior behavior, InputReads reads) {
        if (reads.standsIn(behavior)) {
            return new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT);
        }
        if (reads.entered(behavior)) {
            return new WhyUnread.InACalledBody(WhyUnread.InACalledBody.What.ITSELF);
        }
        boolean hasABody = read.rules().declarations().answers().bodyOf(behavior).isPresent();
        return new WhyUnread.InACalledBody(!hasABody && reads.insideACalledBody()
                ? WhyUnread.InACalledBody.What.WHAT_ITS_DEPENDENCY_ANSWERS
                : WhyUnread.InACalledBody.What.AN_ANSWER_NOT_READ);
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
            case AffineForms.Halt.NotLinear<Quantity, InputReads>(NonAffineOperation operation) ->
                    new WhyUnread.OutsideTheLinearFragment(operation);
            case AffineForms.Halt.NoNumberOnARun<Quantity, InputReads> _ ->
                    new WhyUnread.NoNumberOnARun();
            case AffineForms.Halt.NotHeld<Quantity, InputReads>(UnheldNumber why) ->
                    new WhyUnread.ANumberNotHeld(why);
            // Several values a name stands for, which only values written out are: a closure's
            // parameter applied to each of them. The reading reads a number through such a name
            // once for each value ({@link #aWayInto}), so one met here is past how many readings of
            // one condition are made.
            case AffineForms.Halt.ValuesDisagree<Quantity, InputReads> _ ->
                    new WhyUnread.MoreReadingsThanAreMade();
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
                // An element of a container this reading cannot write out, or of one that holds
                // none, stands at no position.
                case ReadMeaning.Element _, ReadMeaning.NoneHeld _ ->
                        new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.CONTAINER);
                // Read once for each value it can be handed ({@link #aWayInto}), so one met here is
                // past how many readings of one condition are made; and one of a container holding
                // more than is written out is past it before any is.
                case ReadMeaning.OneOf _, ReadMeaning.MoreThanAreWrittenOut _ ->
                        new WhyUnread.MoreReadingsThanAreMade();
                // A name read through is followed above to what it was given, so one that stands
                // here came round to itself.
                case ReadMeaning.Through _, ReadMeaning.Unknown _, ReadMeaning.Position _ ->
                        new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT);
            };
        }
        switch (e) {
            // An operator that is no arithmetic: what it answers is no number of anything.
            case Core.Binary _ -> {
                return new WhyUnread.NotArithmetic();
            }
            // A choice between values, where what is chosen is one of the arms. A number is read
            // through a choice once for each arm ({@link #throughWhatItStopsAt}), so one met here
            // is past how many readings of one condition are made.
            case Core.If _, Core.IfConstructed _, Core.Match _ -> {
                return new WhyUnread.MoreReadingsThanAreMade();
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
                // The same, of an operation the library defines by cases.
                if (!facts.isDefinedByCases(operation).isEmpty()) {
                    yield new WhyUnread.MoreReadingsThanAreMade();
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
