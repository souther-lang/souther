package souther.compiler.check;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.proof.Proof;
import souther.compiler.proof.Slot;
import souther.compiler.proof.Unproved;
import souther.compiler.semantics.Accumulation;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.Arithmetic;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.DefinitionCase;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.MapPart;
import souther.compiler.semantics.NumericResult;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.ResultBound;
import souther.compiler.semantics.SideAnswered;
import souther.compiler.semantics.SizeAgainstItsSource;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.semantics.TakenAs;
import souther.compiler.semantics.Unsayable;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.BinOp;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * What one binding of the declarations came to: every fact about the language's operations, held to
 * a library, keyed by the operation each is about.
 *
 * <p>The one place a fact is looked up. The declarations ({@link
 * souther.compiler.semantics.OperationFacts}) publish a list and no index, so that a reader cannot
 * reach a fact except through what the binder made of it; this is what the binder makes, and a
 * reader that wants a fact asks here. Every value here is a {@link BoundOperationFact}, in which
 * every operation and every argument has already been read against its declaration, so what a
 * reader does with one is use it.
 *
 * <p><b>Keyed by the fact's own operation, and by a name.</b> The key under which a fact is filed is
 * read off the fact — {@code fact.operation().operation()} — and never written beside it, so no key
 * can say the fact is about one operation while the fact says another. And it is the name, because
 * that is the identity of a declaration ({@link souther.compiler.core.DeclaredOperation#equals}) and
 * because a reader holding a call the language resolved but did not keep standing has the name and
 * nothing else. Asking by name is a lookup among values the binding made and not a second reading of
 * the authored word: nothing here reads a declaration, a signature, or an {@link
 * souther.compiler.semantics.ArgumentRef}, and nothing here can be answered for an operation the
 * binding did not hold.
 *
 * <p><b>Bound to bound, and nothing else.</b> The two answers here that are not a plain lookup —
 * what an operation takes of its argument, which operations answer a number taken of one — are put
 * together from bound facts and the derivation those facts carry themselves
 * ({@link BoundOperationFact.AccumulatesItsContainer#takenAs}). No library and no authoring
 * vocabulary is read to answer them, so what they say cannot come apart from what was held.
 *
 * <p>Collected by family. A {@link BoundOperationFact.OneAboutAnOperation} is filed under its
 * operation once and a second of the same kind is refused: it would be two answers to a question
 * that has one, and a map written into keeps whichever arrived last. A
 * {@link BoundOperationFact.SeveralAboutAnOperation} is appended, in the order declared. Which of
 * the two a kind is was chosen where the arm was written, so nothing here has to be told.
 *
 * <p>Filed once, at construction, into what each query answers with. A query is asked per
 * expression per pass, so what it hands back is the list that was filed and not a projection made
 * for the ask.
 */
public final class BoundOperationFacts {

    private final List<BoundOperationFact> held;
    private final Map<Class<? extends BoundOperationFact.OneAboutAnOperation>,
            Map<ValueName, BoundOperationFact.OneAboutAnOperation>> ones = new LinkedHashMap<>();
    private final Map<Class<? extends BoundOperationFact.SeveralAboutAnOperation>,
            Map<ValueName, List<BoundOperationFact.SeveralAboutAnOperation>>> several =
            new LinkedHashMap<>();
    private final Map<ValueName, List<ResultBound<DeclaredArgument>>> bounds;
    private final Map<ValueName, List<DeclaredArgument>> noSmallerThan;
    private final Map<ValueName, List<DefinitionCase<DeclaredArgument>>> cases;
    private final Map<BinOp, List<ValueName>> writtenAs;
    private final Map<ValueName, List<LawProposition<Slot>>> relations;
    private final Stdlib stdlib;
    private final Map<ValueName, Map<OperationLaw.Observed, Settled>> settled;
    private final List<BoundOperationFact> notProvedOfTheirBodies;

    /** Made by the binder and by nothing else: what these are is what a binding came to, and a
     *  set of facts gathered anywhere else would say so of facts nothing bound. Counted from the
     *  class files, as the arms' own constructors are. {@code stdlib} is the library they were
     *  held to, whose written operations' laws are proved against their bodies, by
     *  {@code proofs}. */
    BoundOperationFacts(Stdlib stdlib, List<BoundOperationFact> bound,
                        LibraryProofs.Source proofs) {
        this.stdlib = stdlib;
        this.held = List.copyOf(bound);
        // What is stated of an operation the library writes is filed once its body proves it and
        // not before: a proof reads what is filed here, and a statement not proved is no fact.
        List<BoundOperationFact> awaiting = new ArrayList<>();
        for (BoundOperationFact fact : held) {
            if (writes(fact.operation().operation())) {
                awaiting.add(fact);
            } else {
                file(fact);
            }
        }
        writtenAs = writtenAs();
        relations = relations(projected(BoundOperationFact.IsRelated.class,
                BoundOperationFact.IsRelated::holds), projected(BoundOperationFact.HasALaw.class,
                BoundOperationFact.HasALaw::beside));
        Settling settling = settle(awaiting, proofs);
        settled = settling.settled();
        // One the body does not prove is an obligation, held apart, and no reader takes it. The
        // cases a definition is written in stand or fall together: a reader takes them as every
        // way the operation answers, so they are filed where every one of them is proved and some
        // one of them is reached however the arguments stand ({@link DefinitionCase#coverEveryWay}),
        // and otherwise none of them is.
        List<BoundOperationFact> unproved = new ArrayList<>();
        Map<ValueName, List<BoundOperationFact.IsDefinedByCases>> definitions =
                new LinkedHashMap<>();
        for (BoundOperationFact fact : awaiting) {
            if (fact instanceof BoundOperationFact.IsDefinedByCases one) {
                definitions.computeIfAbsent(one.operation().operation(), _ -> new ArrayList<>())
                        .add(one);
            } else if (settling.proving().proves(fact)) {
                file(fact);
            } else {
                unproved.add(fact);
            }
        }
        definitions.forEach((operation, cases) -> {
            boolean defined = cases.stream().allMatch(settling.proving()::proves)
                    && DefinitionCase.coverEveryWay(cases.stream()
                            .map(BoundOperationFact.IsDefinedByCases::one).toList());
            cases.forEach(defined ? this::file : unproved::add);
        });
        notProvedOfTheirBodies = List.copyOf(unproved);
        // What each query over a family answers with, projected once from what was filed.
        noSmallerThan = projected(BoundOperationFact.ResultIsNoSmallerThan.class,
                BoundOperationFact.ResultIsNoSmallerThan::container);
        bounds = projected(BoundOperationFact.BoundsItsResult.class,
                BoundOperationFact.BoundsItsResult::bound);
        cases = projected(BoundOperationFact.IsDefinedByCases.class,
                BoundOperationFact.IsDefinedByCases::one);
    }

    /** Files {@code fact} under its operation, in its family. */
    private void file(BoundOperationFact fact) {
        ValueName key = fact.operation().operation();
        // No default. A family added is a family this has to say how to collect.
        switch (fact) {
            case BoundOperationFact.OneAboutAnOperation one -> {
                Map<ValueName, BoundOperationFact.OneAboutAnOperation> byOperation =
                        ones.computeIfAbsent(one.getClass(), _ -> new LinkedHashMap<>());
                if (byOperation.put(key, one) != null) {
                    throw new IllegalStateException(key + " is declared to "
                            + one.getClass().getSimpleName() + " twice");
                }
            }
            case BoundOperationFact.SeveralAboutAnOperation many ->
                    several.computeIfAbsent(many.getClass(), _ -> new LinkedHashMap<>())
                            .computeIfAbsent(key, _ -> new ArrayList<>()).add(many);
        }
    }

    /** Which operation computes what each operator computes, read off the arithmetic each of them
     *  declares. */
    private Map<BinOp, List<ValueName>> writtenAs() {
        Map<BinOp, List<ValueName>> out = new LinkedHashMap<>();
        for (ValueName operation : computesANumber()) {
            NumericResult<DeclaredArgument> result = computesANumber(operation);
            BinOp op = result == null ? null : result.computes().writtenAs();
            if (op != null) {
                List<ValueName> computing = out.get(op);
                if (computing == null) {
                    computing = new ArrayList<>();
                    out.put(op, computing);
                }
                computing.add(operation);
            }
        }
        return Collections.unmodifiableMap(out);
    }

    /** The facts of {@code kind} an operation carries, each read as {@code part}, by operation. */
    private <F extends BoundOperationFact.SeveralAboutAnOperation, V> Map<ValueName, List<V>>
            projected(Class<F> kind, Function<F, V> part) {
        Map<ValueName, List<BoundOperationFact.SeveralAboutAnOperation>> byOperation =
                several.getOrDefault(kind, Map.of());
        Map<ValueName, List<V>> out = new LinkedHashMap<>();
        byOperation.forEach((operation, facts) -> {
            List<V> parts = new ArrayList<>(facts.size());
            for (BoundOperationFact.SeveralAboutAnOperation each : facts) {
                parts.add(part.apply(kind.cast(each)));
            }
            out.put(operation, List.copyOf(parts));
        });
        return Collections.unmodifiableMap(out);
    }

    /** What is stated of each kernel beside others: what is declared so, and what its laws say
     *  beside the memberships their cases turn on. */
    private static Map<ValueName, List<LawProposition<Slot>>> relations(
            Map<ValueName, List<LawProposition<Slot>>> declared,
            Map<ValueName, List<List<LawProposition<Slot>>>> besideALaw) {
        Map<ValueName, List<LawProposition<Slot>>> out = new LinkedHashMap<>();
        declared.forEach((operation, holds) -> out.put(operation, new ArrayList<>(holds)));
        besideALaw.forEach((operation, each) -> each.forEach(beside -> {
            if (!beside.isEmpty()) {
                out.computeIfAbsent(operation, _ -> new ArrayList<>()).addAll(beside);
            }
        }));
        out.replaceAll((operation, holds) -> List.copyOf(holds));
        return Collections.unmodifiableMap(out);
    }

    /**
     * Every bound fact, in the order the declarations were held.
     *
     * <p>This package's and not everybody's, and read by two callers — the binder, which asks what
     * it has just bound before publishing it, and {@link NumericReadings}, which counts the
     * representations of a number across every kind of fact — and
     * {@code OnlyTheBinderReadsTheAuthoringVocabularyTest} counts them. Published, this would be
     * a way for a reader to sort the facts for itself and arrive at a second reading of what one
     * of the queries above already answers: a reader that picked the walks out of the list and
     * decided which of them add would own, beside {@link #takenAs}, the question of what a sum
     * is.
     */
    List<BoundOperationFact> all() {
        return held;
    }

    /** Whether any fact is stated of {@code operation}, whatever the fact is about. */
    public boolean statesAnythingOf(ValueName operation) {
        for (BoundOperationFact fact : held) {
            if (fact.operation().operation().equals(operation)) {
                return true;
            }
        }
        return false;
    }

    private <F extends BoundOperationFact.OneAboutAnOperation> F one(Class<F> kind,
                                                                    ValueName operation) {
        Map<ValueName, BoundOperationFact.OneAboutAnOperation> byOperation = ones.get(kind);
        return byOperation == null || operation == null ? null
                : kind.cast(byOperation.get(operation));
    }

    private Set<ValueName> ones(Class<? extends BoundOperationFact.OneAboutAnOperation> kind) {
        Map<ValueName, BoundOperationFact.OneAboutAnOperation> byOperation = ones.get(kind);
        return byOperation == null ? Set.of() : Collections.unmodifiableSet(byOperation.keySet());
    }

    /** What {@code operation} answers, counted, in what its arguments are counted as — or null
     *  where it states no such form. */
    public LinearForm<DeclaredArgument> answersAFormOfItsArguments(ValueName operation) {
        BoundOperationFact.AnswersAFormOfItsArguments held =
                one(BoundOperationFact.AnswersAFormOfItsArguments.class, operation);
        return held == null ? null : held.form();
    }

    /** The operations declared to answer a form of their arguments. */
    public Set<ValueName> answersAFormOfItsArguments() {
        return ones(BoundOperationFact.AnswersAFormOfItsArguments.class);
    }

    /** Which of {@code operation}'s two arguments a positive answer names as the greater, or null
     *  where the sign of what it answers is not their order. */
    public BoundOperationFact.StatesTheOrderOfItsArguments statesTheOrderOfItsArguments(
            ValueName operation) {
        return one(BoundOperationFact.StatesTheOrderOfItsArguments.class, operation);
    }

    /** The operations whose answer states the order of their arguments. */
    public Set<ValueName> statesTheOrderOfItsArguments() {
        return ones(BoundOperationFact.StatesTheOrderOfItsArguments.class);
    }

    /** How {@code operation} moves the value it is given, or null where it moves none. */
    public BoundOperationFact.ShiftsBy shiftsBy(ValueName operation) {
        return one(BoundOperationFact.ShiftsBy.class, operation);
    }

    /** The operations that move a value by an amount. */
    public Set<ValueName> shiftsBy() {
        return ones(BoundOperationFact.ShiftsBy.class);
    }

    /** How {@code operation} counts whole units between its two arguments, or null where it
     *  counts none. */
    public BoundOperationFact.CountsWholeUnitsBetween countsWholeUnitsBetween(
            ValueName operation) {
        return one(BoundOperationFact.CountsWholeUnitsBetween.class, operation);
    }

    /** The operations that count whole units between two values. */
    public Set<ValueName> countsWholeUnitsBetween() {
        return ones(BoundOperationFact.CountsWholeUnitsBetween.class);
    }

    /** What holds of the number {@code operation} answers, wherever it is called, in the order
     *  declared. */
    public List<ResultBound<DeclaredArgument>> boundsOnTheResult(ValueName operation) {
        return operation == null ? List.of() : bounds.getOrDefault(operation, List.of());
    }

    /** The operations something holds of the result of. */
    public Set<ValueName> boundsOnTheResult() {
        return bounds.keySet();
    }

    /** What {@code operation} builds its result from, or null where it builds none. */
    public BuiltFrom<DeclaredArgument> buildsItsResultFrom(ValueName operation) {
        BoundOperationFact.BuildsItsResultFrom held =
                one(BoundOperationFact.BuildsItsResultFrom.class, operation);
        return held == null ? null : held.built();
    }

    /** The operations that build a container out of another. */
    public Set<ValueName> buildsItsResultFrom() {
        return ones(BoundOperationFact.BuildsItsResultFrom.class);
    }

    /**
     * The argument whose elements the answer of {@code operation} is made from where that is all
     * the operation says, or null where it says more or says nothing.
     *
     * <p>An operation with a building says it there ({@link BuiltFrom#derivesItsElementsFrom}), and
     * a reader that has already fetched the building asks it and comes here only without one. This
     * is the lineage declared apart from a count, which is what an operation answering any number
     * for each element states.
     */
    public DeclaredArgument elementsMadeFromAlone(ValueName operation) {
        BoundOperationFact.ElementsComeFrom held =
                one(BoundOperationFact.ElementsComeFrom.class, operation);
        return held == null ? null : held.lineage().source().argument();
    }

    /** Which part of which map {@code operation} answers a list of, or null where it lists no
     *  map's. */
    public Listed listsAPartOf(ValueName operation) {
        BoundOperationFact.ListsAPartOf held =
                one(BoundOperationFact.ListsAPartOf.class, operation);
        return held == null ? null : new Listed(held.map(), held.part());
    }

    /** A map an operation answers a list of what it holds, and which part of it. */
    public record Listed(DeclaredArgument map, MapPart part) {}

    /** The argument the elements of {@code operation}'s answer stand in the order of, or null
     *  where nothing says they do. */
    public DeclaredArgument keepsTheOrderOf(ValueName operation) {
        BoundOperationFact.KeepsTheOrderOf held =
                one(BoundOperationFact.KeepsTheOrderOf.class, operation);
        return held == null ? null : held.source();
    }

    /** Which argument {@code operation} puts in which, or null where it puts nothing in. Read by
     *  the proofs of what the library's written operations build, and by no reader of a
     *  condition. */
    BoundOperationFact.PutsAValueIn putsAValueIn(ValueName operation) {
        return one(BoundOperationFact.PutsAValueIn.class, operation);
    }

    /** The map whose keys {@code operation} answers a map keyed by, or null where it keeps none. */
    public DeclaredArgument keepsTheKeysOf(ValueName operation) {
        BoundOperationFact.KeepsTheKeysOf held =
                one(BoundOperationFact.KeepsTheKeysOf.class, operation);
        return held == null ? null : held.map();
    }

    /**
     * How the observation {@code observed} of {@code operation}'s answer is settled, or null where
     * nothing settles it.
     *
     * <p>The one place this is asked, and one answer to it: a law declared, a law derived from what
     * the operation is declared to build, or a closing. An answer as many as the one source it was
     * built from holds something where that source does and is as many as it — and so is a list of
     * what a map holds — so those laws are read off that declaration, and one declared beside it is
     * refused where these are collected, as is a law beside a closing.
     */
    public Settled settled(ValueName operation, OperationLaw.Observed observed) {
        Map<OperationLaw.Observed, Settled> of = operation == null ? null : settled.get(operation);
        return of == null ? null : of.get(observed);
    }

    /** What is stated of operations the library writes that their bodies do not prove, and that
     *  no query answers with. */
    List<BoundOperationFact> notProvedOfTheirBodies() {
        return notProvedOfTheirBodies;
    }

    /** The operations some observation of whose answer is settled, each with how. */
    public Map<ValueName, Map<OperationLaw.Observed, Settled>> settled() {
        return settled;
    }

    /** How an observation of an operation's answer is settled. */
    public sealed interface Settled {

        /** By {@code law}, standing on {@code grounds}. */
        record ByALaw(OperationLaw<DeclaredArgument> law, Grounds grounds) implements Settled {}

        /** By a closing: it comes to {@code why}, which no statement over the arguments says. */
        record Unsaid(Unsayable why) implements Settled {}

        /**
         * By nothing: what was stated of it ({@code stated}, null where it was a closing) is not
         * proved against the body, for {@code why}. An obligation and no law, which no reader takes.
         */
        record Open(OperationLaw<DeclaredArgument> stated, Unproved why) implements Settled {}
    }

    /** What a law stands on. */
    public sealed interface Grounds {

        /** It is declared of a kernel, which has no body to prove it of: an axiom, held to what the
         *  kernel computes by running it. */
        record Axiom() implements Grounds {}

        /** It is read off what a kernel is declared to build: as many as one source, or a list of a
         *  part of a map. An axiom all the same, said once. */
        record WhatItBuilds() implements Grounds {}

        /** It is proved against the operation's body, as {@code proof} says. */
        record Proved(Proof proof) implements Grounds {}

        /** It was proved against the operation's body when this compiler was built, which is
         *  what the proofs shipped with it record ({@link LibraryProofsAsBuilt}). */
        record ProvedWhenBuilt() implements Grounds {}
    }

    /** Every settling, read once off the facts: what is declared of the kernels and what follows
     *  from what they are declared to build, and what is proved of the operations the library
     *  writes in the language. */
    private Settling settle(List<BoundOperationFact> awaiting, LibraryProofs.Source proofs) {
        Map<ValueName, Map<OperationLaw.Observed, Settled>> out = new LinkedHashMap<>();
        Map<ValueName.Stdlib.Operation, Map<OperationLaw.Observed, ProvingTheLibrary.Stated>>
                stated = new LinkedHashMap<>();
        for (BoundOperationFact fact : held) {
            ValueName operation = fact.operation().operation();
            Settled settling;
            OperationLaw.Observed observed;
            switch (fact) {
                case BoundOperationFact.HasALaw law -> {
                    settling = new Settled.ByALaw(law.law(), new Grounds.Axiom());
                    observed = law.law().observed();
                }
                case BoundOperationFact.LeavesUnsaid unsaid when writes(operation) -> {
                    put(stated, operation, unsaid.observed(),
                            new ProvingTheLibrary.Stated(null, List.of(), unsaid.why()));
                    continue;
                }
                case BoundOperationFact.LeavesUnsaid unsaid -> {
                    settling = new Settled.Unsaid(unsaid.why());
                    observed = unsaid.observed();
                }
                case BoundOperationFact.HasALemma lemma -> {
                    put(stated, operation, lemma.states().observed(),
                            new ProvingTheLibrary.Stated(lemma.states(), lemma.carries(), null));
                    continue;
                }
                default -> {
                    continue;
                }
            }
            if (out.computeIfAbsent(operation, _ -> new LinkedHashMap<>())
                    .put(observed, settling) != null) {
                throw new IllegalStateException(operation + " settles what "
                        + observed + " of its answer comes to twice");
            }
        }
        for (BoundOperationFact fact : held) {
            ValueName operation = fact.operation().operation();
            if (writes(operation)) {
                continue;   // what a body builds is proved of it, not read off a declaration
            }
            for (OperationLaw<DeclaredArgument> law : derivedFrom(fact)) {
                if (out.computeIfAbsent(operation, _ -> new LinkedHashMap<>())
                        .put(law.observed(), new Settled.ByALaw(law, new Grounds.WhatItBuilds()))
                        != null) {
                    throw new IllegalStateException(operation + " is declared to be something"
                            + " that says what " + law.observed() + " of its answer comes to,"
                            + " and settles it again");
                }
            }
        }
        LibraryProofs proving = proofs.over(stdlib, this, out, stated, awaiting);
        stated.forEach((operation, of) -> of.keySet().forEach(observed ->
                out.computeIfAbsent(operation, _ -> new LinkedHashMap<>())
                        .put(observed, proving.settle(operation, observed))));
        Map<ValueName, Map<OperationLaw.Observed, Settled>> fixed = new LinkedHashMap<>();
        out.forEach((operation, of) -> fixed.put(operation, Collections.unmodifiableMap(of)));
        return new Settling(Collections.unmodifiableMap(fixed), proving);
    }

    /** The settlings, with what proved those of the operations the library writes, which proves
     *  what else is stated of them. */
    private record Settling(Map<ValueName, Map<OperationLaw.Observed, Settled>> settled,
                            LibraryProofs proving) {}

    /** Whether {@code operation} is one the library writes in the language. */
    private boolean writes(ValueName operation) {
        return operation instanceof ValueName.Stdlib.Operation library
                && stdlib.helpers().containsKey(library);
    }

    private static void put(
            Map<ValueName.Stdlib.Operation, Map<OperationLaw.Observed, ProvingTheLibrary.Stated>>
                    stated, ValueName operation, OperationLaw.Observed observed,
            ProvingTheLibrary.Stated what) {
        if (stated.computeIfAbsent((ValueName.Stdlib.Operation) operation,
                _ -> new LinkedHashMap<>()).put(observed, what) != null) {
            throw new IllegalStateException(operation + " states what " + observed
                    + " of its answer comes to twice");
        }
    }

    /** What is stated of {@code operation}'s answer beside what other kernels answer, in the
     *  words of a walk, for the proofs of the library's written operations. */
    List<LawProposition<Slot>> relationsOf(ValueName operation) {
        return operation == null ? List.of() : relations.getOrDefault(operation, List.of());
    }

    /**
     * The laws {@code fact} says by being declared: an answer as many as one source holds
     * something where that source does and is as many as it, and an emptiness check comes out
     * true where its argument holds nothing.
     */
    private static List<OperationLaw<DeclaredArgument>> derivedFrom(BoundOperationFact fact) {
        if (fact instanceof BoundOperationFact.MeansTheSameAsASizeOfNought means) {
            return List.of(new OperationLaw.Observation<>(AnswerAspect.TRUTH,
                    new LawProposition.Observed<>(new LawSubject.Argument<>(means.of()),
                            new SideAnswered(AnswerAspect.EMPTINESS, false))));
        }
        DeclaredArgument source = soleSource(fact);
        if (source == null) {
            return List.of();
        }
        LawSubject<DeclaredArgument> it = new LawSubject.Argument<>(source);
        return List.of(
                new OperationLaw.Observation<>(AnswerAspect.EMPTINESS,
                        new LawProposition.Observed<>(it,
                                new SideAnswered(AnswerAspect.EMPTINESS, true))),
                new OperationLaw.Size<>(LinearForm.atom(new LawNumber.SizeOf<>(it))));
    }

    /** The one argument {@code fact} says the answer is as many as, or null where it says no
     *  such thing: a building of exactly as many from one source, or a list of a map's parts. */
    private static DeclaredArgument soleSource(BoundOperationFact fact) {
        return switch (fact) {
            case BoundOperationFact.BuildsItsResultFrom builds ->
                    builds.built().outputs().size() == 1
                            && builds.built().size() == SizeAgainstItsSource.SAME
                            ? builds.built().lineage().source().argument() : null;
            case BoundOperationFact.ListsAPartOf lists -> lists.map();
            default -> null;
        };
    }

    /** The containers {@code operation}'s result is never smaller than, in the order declared. */
    public List<DeclaredArgument> resultIsNoSmallerThan(ValueName operation) {
        return operation == null ? List.of() : noSmallerThan.getOrDefault(operation, List.of());
    }

    /** Where {@code operation} reads the container its predicate is about, or null where it is no
     *  such predicate. */
    public BoundOperationFact.ReadsItsContainer readsItsContainer(ValueName operation) {
        return one(BoundOperationFact.ReadsItsContainer.class, operation);
    }

    /** The operations that are predicates over what a container holds. */
    public Set<ValueName> readsItsContainer() {
        return ones(BoundOperationFact.ReadsItsContainer.class);
    }

    /** Where {@code operation}'s predicate is stated over a projection, or null where it is stated
     *  over the element itself. */
    public DeclaredArgument isStatedOverAProjection(ValueName operation) {
        BoundOperationFact.IsStatedOverAProjection held =
                one(BoundOperationFact.IsStatedOverAProjection.class, operation);
        return held == null ? null : held.projection();
    }

    /** The operations whose predicate is stated over a projection. */
    public Set<ValueName> isStatedOverAProjection() {
        return ones(BoundOperationFact.IsStatedOverAProjection.class);
    }

    /**
     * Whether {@code operation} comes out true exactly where its first argument does not: a
     * denial, as the law settling its truth says.
     */
    public boolean deniesItsArgument(ValueName operation) {
        return settled(operation, OperationLaw.Observed.TRUTH)
                instanceof Settled.ByALaw(OperationLaw.Observation<DeclaredArgument>(
                        AnswerAspect aspect, LawProposition.Observed<DeclaredArgument>(
                                LawSubject.Argument<DeclaredArgument>(DeclaredArgument of),
                                SideAnswered side)), var _)
                && aspect == AnswerAspect.TRUTH && side.aspect() == AnswerAspect.TRUTH
                && !side.holds() && of.position() == 0;
    }

    /**
     * Where {@code operation} comes out true exactly where no two elements of a container it is
     * handed come to one answer of a closure it is handed: which argument is the container and
     * which the closure — or null where it states no such thing.
     *
     * <p>Read off the law its body is proved to come to: as many different answers of that closure
     * on the container's elements as the container holds elements.
     */
    public NoTwoAlike statesNoTwoAlike(ValueName operation) {
        if (!(settled(operation, OperationLaw.Observed.TRUTH) instanceof Settled.ByALaw(
                OperationLaw.Observation<DeclaredArgument>(var _,
                        LawProposition.Compared<DeclaredArgument>(var form, Rel states)), var _))
                || states != Rel.EQ || !form.constant().isZero() || form.coefs().size() != 2) {
            return null;
        }
        DeclaredArgument container = null;
        DeclaredArgument by = null;
        DeclaredArgument sized = null;
        ExactRatio different = null;
        ExactRatio size = null;
        for (var term : form.coefs().entrySet()) {
            switch (term.getKey()) {
                case LawNumber.HowManyDifferent<DeclaredArgument>(var over,
                        LawSubject.WhatTheClosureAnswers<DeclaredArgument>(var closure)) -> {
                    container = over;
                    by = closure;
                    different = term.getValue();
                }
                case LawNumber.SizeOf<DeclaredArgument>(
                        LawSubject.Argument<DeclaredArgument>(var of)) -> {
                    sized = of;
                    size = term.getValue();
                }
                default -> {
                    return null;
                }
            }
        }
        return container == null || !container.equals(sized)
                || !different.negated().equals(size) ? null : new NoTwoAlike(container, by);
    }

    /** The container no two elements of which are alike, and the closure whose answers they are
     *  alike by. */
    public record NoTwoAlike(DeclaredArgument container, DeclaredArgument by) {}

    /** Whether {@code operation} states its predicate of every element. */
    public boolean statesItsPredicateOfEveryElement(ValueName operation) {
        return one(BoundOperationFact.StatesItsPredicateOfEveryElement.class, operation) != null;
    }

    /** The operations that do. */
    public Set<ValueName> statesItsPredicateOfEveryElement() {
        return ones(BoundOperationFact.StatesItsPredicateOfEveryElement.class);
    }

    /** The rewrite an emptiness check stands for, or null where {@code operation} is not one. */
    public BoundOperationFact.MeansTheSameAsASizeOfNought meansTheSameAsASizeOfNought(
            ValueName operation) {
        return one(BoundOperationFact.MeansTheSameAsASizeOfNought.class, operation);
    }

    /** The emptiness checks. */
    public Set<ValueName> meansTheSameAsASizeOfNought() {
        return ones(BoundOperationFact.MeansTheSameAsASizeOfNought.class);
    }

    /** What {@code operation} computes and where it answers it, or null where it computes no
     *  arithmetic of its own. */
    public NumericResult<DeclaredArgument> computesANumber(ValueName operation) {
        BoundOperationFact.ComputesANumber held =
                one(BoundOperationFact.ComputesANumber.class, operation);
        return held == null ? null : held.result();
    }

    /** The operations that compute arithmetic of their own. */
    public Set<ValueName> computesANumber() {
        return ones(BoundOperationFact.ComputesANumber.class);
    }

    /**
     * The operations computing what {@code op} computes, in the order the facts were declared.
     *
     * <p>What a reader has when it holds an operator and wants the operation whose account says how
     * such a number is read and built. What an operator computes is declared with the arithmetic
     * ({@link Arithmetic#writtenAs}), so this is an index over the declarations and not a second
     * list of which operation an operator reaches.
     *
     * <p><b>All of them, because which one a call reached is the call's to settle.</b> An operator
     * is written over whatever numbers the language has — the same {@code +} adds two whole numbers
     * and two decimals — so the operations computing one arithmetic are as many as there are kinds
     * of number, and a reader holding a call knows which kind it answered. Answered here as "one,
     * or none where there are two", the first pair to arrive for an operator would take the answer
     * away from every call of it, including the calls that were never ambiguous.
     */
    public List<ValueName> computing(BinOp op) {
        return writtenAs.getOrDefault(op, List.of());
    }

    /** The cases {@code operation}'s definition is written in, in the order declared, or an empty
     *  list where it answers none of the values it was given. */
    public List<DefinitionCase<DeclaredArgument>> isDefinedByCases(ValueName operation) {
        return operation == null ? List.of() : cases.getOrDefault(operation, List.of());
    }

    /** The operations that answer one of the values they were given. */
    public Set<ValueName> isDefinedByCases() {
        return cases.keySet();
    }

    /** What walking {@code operation}'s container comes to, and over which argument — or null where
     *  it accumulates nothing, including where the name is no operation of the library. */
    public BoundOperationFact.AccumulatesItsContainer accumulates(ValueName operation) {
        return one(BoundOperationFact.AccumulatesItsContainer.class, operation);
    }

    /** What walking {@code operation}'s container comes to, or null where it accumulates nothing. */
    public Accumulation accumulation(ValueName operation) {
        BoundOperationFact.AccumulatesItsContainer held = accumulates(operation);
        return held == null ? null : held.how();
    }

    /** The operations that answer what a container holds accumulated. */
    public Set<ValueName> accumulates() {
        return ones(BoundOperationFact.AccumulatesItsContainer.class);
    }

    /** The number {@code operation} is declared to answer, taken of which of its arguments, or
     *  null where none is declared. */
    BoundOperationFact.AnswersANumberTakenOfAValueItIsGiven numberTakenOf(ValueName operation) {
        return one(BoundOperationFact.AnswersANumberTakenOfAValueItIsGiven.class, operation);
    }

    /**
     * What {@code operation} takes of a value it is given whatever else it is given, or null where
     * the number it answers is not taken of one value at all.
     *
     * <p>Declared, or read off the walk where the operation is one — and the second is the walk's
     * own reading ({@link BoundOperationFact.AccumulatesItsContainer#takenAs}), put beside the first
     * here so that a reader asks one question. That the two cannot both hold of one operation is
     * held where the declarations are bound ({@link NumericReadings}).
     */
    public TakenAs takenAs(ValueName operation) {
        BoundOperationFact.AnswersANumberTakenOfAValueItIsGiven declared =
                one(BoundOperationFact.AnswersANumberTakenOfAValueItIsGiven.class, operation);
        if (declared != null) {
            return declared.how();
        }
        BoundOperationFact.AccumulatesItsContainer walk = accumulates(operation);
        return walk == null ? null : walk.takenAs();
    }

    /**
     * The same for one call, where {@code arguments} is what the call's other arguments read as.
     *
     * <p><b>Two questions, one wider than the other.</b> What an operation takes of a value it is
     * given is a fact about the operation and is what {@link #takenAs(ValueName)} answers; whether
     * a <em>call</em> of it is a number taken of one position can turn on what the call was given —
     * a quotient by a written constant is such a number and a quotient by a name is not. So the
     * second is asked with the arguments in hand, and the population an operation-level reader walks
     * ({@link #answersANumberTakenOfItsArgument}) is the first and stays as wide as it was.
     *
     * <p>Derived and not declared. The account for such a call comes off the representation the
     * operation already has ({@link BoundOperationFact.ComputesANumber#takenAs}), so the library
     * still reads one operation's number one way and nothing here is a second account of it.
     */
    public TakenAs takenAs(ValueName operation, TakenArguments arguments) {
        TakenAs declared = takenAs(operation);
        if (declared != null) {
            return declared;
        }
        BoundOperationFact.ComputesANumber computes =
                one(BoundOperationFact.ComputesANumber.class, operation);
        return computes == null ? null : computes.takenAs(arguments);
    }

    /**
     * The operations that answer a number taken of a value they are given, whatever else they are
     * given.
     *
     * <p>The ones {@link #takenAs(ValueName)} answers for, which is not the same as the ones an
     * account is declared of: a walk that adds up a container is read as one and its account is
     * that walk. Nor is it every operation some call of which is such a number: an account a call's
     * own arguments settle belongs to the call ({@link #takenAs(ValueName, TakenArguments)}), and a
     * reader walking operations is not holding one.
     */
    public Set<ValueName> answersANumberTakenOfItsArgument() {
        Set<ValueName> out = new LinkedHashSet<>(
                ones(BoundOperationFact.AnswersANumberTakenOfAValueItIsGiven.class));
        for (ValueName operation : accumulates()) {
            if (takenAs(operation) != null) {
                out.add(operation);
            }
        }
        return Collections.unmodifiableSet(out);
    }

    /** The operations that count what they are given, which is the narrower vocabulary a size is
     *  asked for under. Read off the account rather than declared beside it. */
    public Set<ValueName> countsWhatItIsGiven() {
        Set<ValueName> out = new LinkedHashSet<>();
        for (ValueName operation
                : ones(BoundOperationFact.AnswersANumberTakenOfAValueItIsGiven.class)) {
            if (takenAs(operation) instanceof TakenAs.HowManyItHolds) {
                out.add(operation);
            }
        }
        return Collections.unmodifiableSet(out);
    }

    /** Whether every number {@code operation} could answer is one some value it could be given
     *  answers. */
    public boolean everyAnswerItCanGiveHasASourceValue(ValueName operation) {
        return one(BoundOperationFact.EveryAnswerItCanGiveHasASourceValue.class, operation) != null;
    }
}
