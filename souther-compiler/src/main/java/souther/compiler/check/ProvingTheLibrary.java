package souther.compiler.check;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.proof.AppliedClosures;
import souther.compiler.proof.ByPlace;
import souther.compiler.proof.Lemma;
import souther.compiler.proof.Library;
import souther.compiler.proof.LibraryProver;
import souther.compiler.proof.Slot;
import souther.compiler.proof.Unproved;
import souther.compiler.proof.WalksFromASeed;
import souther.compiler.proof.WhatAClosingIsAbout;
import souther.compiler.proof.WhatAStatementSurvives;
import souther.compiler.proof.WhatItAccumulates;
import souther.compiler.proof.WhereTheElementsCameFrom;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.ArgumentsStand;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.ClosurePositions;
import souther.compiler.semantics.DefinitionCase;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.ResultBound;
import souther.compiler.semantics.SideAnswered;
import souther.compiler.semantics.TakenAs;
import souther.compiler.semantics.Unsayable;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The laws of the operations the library writes in the language, settled by proving what is stated
 * of each against its body.
 *
 * <p>Asked one observation at a time and settled on the first ask, since a proof of one operation
 * reads the laws of those its body calls, and those are settled by proofs of their own. A kernel's
 * law is what it is declared; nothing else is a law here until a proof makes it one. A proof that
 * would read, on the way, the law it is proving is a circle, and it is left open rather than taken.
 */
final class ProvingTheLibrary {

    /** What is stated of one operation the library writes, waiting to be proved. */
    record Stated(OperationLaw<DeclaredArgument> law, List<LawProposition<Slot>> carries,
                  Unsayable closedAs) {}

    private final Stdlib stdlib;
    private final BoundOperationFacts facts;
    private final Map<ValueName, Map<OperationLaw.Observed, BoundOperationFacts.Settled>> kernels;
    private final Map<ValueName.Stdlib.Operation, Map<OperationLaw.Observed, Stated>> stated;
    private final Map<ValueName.Stdlib.Operation, BuiltFrom<DeclaredArgument>> builds =
            new HashMap<>();
    /** What each is stated to answer beside what others answer: the lemmas stated so, and what
     *  keeping a map's keys states. */
    private final Map<ValueName.Stdlib.Operation, List<Related>> relates = new HashMap<>();
    /** Every statement of what a walk in each one's body carries, as each lemma states it. */
    private final Map<ValueName.Stdlib.Operation, List<List<LawProposition<Slot>>>> carries =
            new HashMap<>();
    private final Map<ValueName.Stdlib.Operation, Map<OperationLaw.Observed,
            BoundOperationFacts.Settled>> settled = new HashMap<>();
    private final Map<ValueName.Stdlib.Operation, Boolean> provedToBuild = new HashMap<>();
    private final Map<List<Object>, Boolean> provedToRelate = new HashMap<>();
    private final Set<List<Object>> underWay = new HashSet<>();
    private final LibraryProver prover;
    private final WhereTheElementsCameFrom elements;
    private final WhatItAccumulates accumulated;
    private final WhatAClosingIsAbout closings;

    /**
     * @param awaiting every fact stated of an operation the library writes, waiting to be proved
     */
    ProvingTheLibrary(Stdlib stdlib, BoundOperationFacts facts,
                      Map<ValueName, Map<OperationLaw.Observed, BoundOperationFacts.Settled>> kernels,
                      Map<ValueName.Stdlib.Operation, Map<OperationLaw.Observed, Stated>> stated,
                      List<BoundOperationFact> awaiting) {
        this.stdlib = stdlib;
        this.facts = facts;
        this.kernels = kernels;
        this.stated = stated;
        for (BoundOperationFact fact : awaiting) {
            ValueName.Stdlib.Operation operation =
                    (ValueName.Stdlib.Operation) fact.operation().operation();
            switch (fact) {
                case BoundOperationFact.BuildsItsResultFrom building ->
                        builds.put(operation, building.built());
                case BoundOperationFact.HasARelatedLemma lemma -> {
                    relates.computeIfAbsent(operation, _ -> new ArrayList<>())
                            .add(new Related(lemma.holds(), lemma.carries()));
                    carries.computeIfAbsent(operation, _ -> new ArrayList<>())
                            .add(lemma.carries());
                }
                case BoundOperationFact.KeepsTheKeysOf kept ->
                        relates.computeIfAbsent(operation, _ -> new ArrayList<>())
                                .add(new Related(kept.states(), null));
                case BoundOperationFact.HasALemma lemma ->
                        carries.computeIfAbsent(operation, _ -> new ArrayList<>())
                                .add(lemma.carries());
                default -> { }
            }
        }
        Library library = new LibraryUnderProof(stdlib, facts, this::forAProof, this::builtFrom,
                this::relationsOf);
        Set<ValueName.Stdlib.Operation> walks = new LinkedHashSet<>(WalksFromASeed.of(stdlib,
                AppliedClosures.of(stdlib, Combinators.kernelsIn(stdlib),
                        operation -> Combinators.listing(stdlib, facts, operation),
                        Combinators::positionsOf)).keySet());
        walks.remove(stdlib.walk().operation());
        this.prover = new LibraryProver(library, walks);
        this.elements = new WhereTheElementsCameFrom(library, walks);
        this.accumulated = new WhatItAccumulates(library, walks);
        this.closings = new WhatAClosingIsAbout(library, walks);
    }

    /**
     * Whether {@code fact}, stated of an operation the library writes, is proved against its body
     * — by the procedure that proves a statement of its kind.
     *
     * <p>No default. A kind of fact added is one this says how to prove of a body, or says has no
     * proof here; a statement nothing proves is no fact, and is filed nowhere a reader looks.
     */
    boolean proves(BoundOperationFact fact) {
        ValueName.Stdlib.Operation operation =
                (ValueName.Stdlib.Operation) fact.operation().operation();
        return switch (fact) {
            case BoundOperationFact.BoundsItsResult bounded -> bounds(operation, bounded.bound());
            case BoundOperationFact.IsDefinedByCases defined ->
                    answersInTheCase(operation, defined.one());
            case BoundOperationFact.BuildsItsResultFrom _ -> builds(operation);
            case BoundOperationFact.KeepsTheOrderOf kept ->
                    elements.inOrder(operation, kept.source().position())
                            instanceof LibraryProver.Outcome.Proved;
            // What these state is settled where it is proved, and read from there; filed, they
            // are read by nothing.
            case BoundOperationFact.HasALemma _ -> true;
            case BoundOperationFact.LeavesUnsaid _ -> true;
            case BoundOperationFact.KeepsTheKeysOf kept ->
                    relates(operation, new Related(kept.states(), null));
            case BoundOperationFact.HasARelatedLemma lemma ->
                    relates(operation, new Related(lemma.holds(), lemma.carries()));
            case BoundOperationFact.ResultIsNoSmallerThan bounded ->
                    prover.noSmallerThan(operation, bounded.container().position())
                            instanceof LibraryProver.Outcome.Proved;
            case BoundOperationFact.AccumulatesItsContainer accumulates ->
                    accumulated.prove(operation, accumulates.container().position(),
                            accumulates.how()) instanceof LibraryProver.Outcome.Proved;
            case BoundOperationFact.ReadsItsContainer reads -> survives(operation, reads);
            case BoundOperationFact.IsStatedOverAProjection over ->
                    overAProjection(operation, over.projection());
            case BoundOperationFact.StatesItsPredicateOfEveryElement _ -> ofEveryElement(operation);
            case BoundOperationFact.MeansTheSameAsASizeOfNought means -> sizeOfNought(operation,
                    means);
            // A kernel's, which an operation with a body is refused where the facts are bound, or
            // a statement no body here is proved to make.
            case BoundOperationFact.HasALaw _ -> false;
            case BoundOperationFact.IsRelated _ -> false;
            case BoundOperationFact.PutsAValueIn _ -> false;
            case BoundOperationFact.ListsAPartOf _ -> false;
            case BoundOperationFact.AnswersAFormOfItsArguments _ -> false;
            case BoundOperationFact.StatesTheOrderOfItsArguments _ -> false;
            case BoundOperationFact.ShiftsBy _ -> false;
            case BoundOperationFact.AnswersANumberTakenOfAValueItIsGiven _ -> false;
            case BoundOperationFact.EveryAnswerItCanGiveHasASourceValue _ -> false;
            case BoundOperationFact.ComputesANumber _ -> false;
        };
    }

    /** The law {@code observed} of {@code operation}'s answer is settled by, over its arguments by
     *  place, or null where no law settles it. */
    private OperationLaw<Integer> lawOf(ValueName.Stdlib.Operation operation,
                                        OperationLaw.Observed observed) {
        return settle(operation, observed) instanceof BoundOperationFacts.Settled.ByALaw(
                var law, var _) ? ByPlace.law(law, DeclaredArgument::position) : null;
    }

    /**
     * Whether what {@code operation}'s answer comes out true for survives every construction
     * {@code reads} names: read off the law its body proves, or off the closing it proves, where
     * that is about the container named.
     */
    private boolean survives(ValueName.Stdlib.Operation operation,
                             BoundOperationFact.ReadsItsContainer reads) {
        int container = reads.container().position();
        if (settle(operation, OperationLaw.Observed.TRUTH)
                instanceof BoundOperationFacts.Settled.Unsaid(Unsayable why)) {
            ClosurePositions at = Combinators.positionsOf(operation);
            return aboutTheContainer(why) && about(operation, why) && at != null
                    && at.containerArg() == container
                    && reads.through().stream().allMatch(why::survives);
        }
        if (!(lawOf(operation, OperationLaw.Observed.TRUTH)
                instanceof OperationLaw.Observation<Integer>(var _, LawProposition<Integer> holds))) {
            return false;
        }
        return reads.through().stream().allMatch(shape ->
                WhatAStatementSurvives.survives(holds, container, shape));
    }

    /** Whether {@code operation}'s answer comes out true by a closing about a closure's answer on
     *  each element of its container, and the closure is the one at {@code projection}. */
    private boolean overAProjection(ValueName.Stdlib.Operation operation,
                                    DeclaredArgument projection) {
        ClosurePositions at = Combinators.positionsOf(operation);
        return at != null && at.closureArg() == projection.position()
                && settle(operation, OperationLaw.Observed.TRUTH)
                instanceof BoundOperationFacts.Settled.Unsaid(Unsayable why)
                && aboutTheContainer(why) && about(operation, why);
    }

    /**
     * Whether a closing for {@code why} is about the operation's container and closure, which the
     * closing's proof shows of the body ({@link #about}).
     */
    private static boolean aboutTheContainer(Unsayable why) {
        return switch (why) {
            case NO_TWO_ELEMENTS_ALIKE -> true;
            case EVERY_CHARACTER_IS_WHITESPACE, A_KEY_OF_A_MAP, MADE_UP_OF_COPIES_OF_A_TEXT,
                 A_STRING_INSIDE_ANOTHER, A_STRING_MATCHING_A_PATTERN, HOW_MANY_DIFFERENT_VALUES ->
                    false;
        };
    }

    /**
     * Whether the body of {@code operation} comes to {@code why} about what the closing says it is
     * about: for a closing about the operation's container and closure, about those two, as the
     * body says; for any other, nothing beyond the proposition.
     */
    private boolean about(ValueName.Stdlib.Operation operation, Unsayable why) {
        if (!aboutTheContainer(why)) {
            return true;
        }
        ClosurePositions at = Combinators.positionsOf(operation);
        return at != null && closings.noTwoAlike(operation, at.containerArg(), at.closureArg())
                instanceof LibraryProver.Outcome.Proved;
    }

    /** Whether {@code operation} comes out true exactly where no element of its container is one
     *  its closure answers false of, as the law its body proves says. */
    private boolean ofEveryElement(ValueName.Stdlib.Operation operation) {
        ClosurePositions at = Combinators.positionsOf(operation);
        return at != null && new OperationLaw.Observation<>(AnswerAspect.TRUTH,
                new LawProposition.SomeElement<>(at.containerArg(), new LawProposition.Observed<>(
                        new LawSubject.WhatTheClosureAnswers<>(at.closureArg()),
                        new SideAnswered(AnswerAspect.TRUTH, false)), false))
                .equals(lawOf(operation, OperationLaw.Observed.TRUTH));
    }

    /** Whether {@code operation} comes out true exactly where its argument holds nothing, as the
     *  law its body proves says, and the operation it means the same as answers how many that
     *  argument holds. */
    private boolean sizeOfNought(ValueName.Stdlib.Operation operation,
                                 BoundOperationFact.MeansTheSameAsASizeOfNought means) {
        BoundOperationFact.AnswersANumberTakenOfAValueItIsGiven size =
                facts.numberTakenOf(means.size().operation());
        return size != null && size.how() instanceof TakenAs.HowManyItHolds
                && new OperationLaw.Observation<>(AnswerAspect.TRUTH, new LawProposition.Observed<>(
                        new LawSubject.Argument<>(means.of().position()),
                        new SideAnswered(AnswerAspect.EMPTINESS, false)))
                .equals(lawOf(operation, OperationLaw.Observed.TRUTH));
    }

    /**
     * A statement of an operation's answer beside what others answer, and what its walk is stated
     * to carry for a proof of it: its own lemma's statement, or — for one no lemma states, null
     * here — any lemma's of the operation.
     */
    private record Related(LawProposition<Slot> holds, List<LawProposition<Slot>> carried) {}

    /** Whether {@code related}, stated of {@code operation}'s answer, is proved against its
     *  body. */
    private boolean relates(ValueName.Stdlib.Operation operation, Related related) {
        List<Object> asking = List.of(operation, related.holds());
        Boolean done = provedToRelate.get(asking);
        if (done != null) {
            return done;
        }
        if (!underWay.add(asking)) {
            return false;   // a proof reading what it is proving: nothing settles it yet
        }
        boolean proved = prover.relates(operation, related.holds(),
                related.carried() != null ? List.of(related.carried())
                        : carries.getOrDefault(operation, List.of()))
                instanceof LibraryProver.Outcome.Proved;
        underWay.remove(asking);
        provedToRelate.put(asking, proved);
        return proved;
    }

    /** What is stated of {@code operation}'s answer beside what others answer, as a proof may take
     *  it: an axiom of a kernel, and of an operation the library writes only once proved. */
    private List<LawProposition<Slot>> relationsOf(ValueName.Stdlib.Operation operation) {
        if (!stdlib.helpers().containsKey(operation)) {
            return facts.relationsOf(operation);
        }
        List<LawProposition<Slot>> out = new ArrayList<>();
        for (Related each : relates.getOrDefault(operation, List.of())) {
            if (relates(operation, each)) {
                out.add(each.holds());
            }
        }
        return out;
    }

    /** What {@code operation} builds its answer from, as a proof may take it: declared of a kernel,
     *  and of an operation the library writes only once proved of its body. */
    private BuiltFrom<Integer> builtFrom(ValueName.Stdlib.Operation operation) {
        BuiltFrom<DeclaredArgument> built = stdlib.helpers().containsKey(operation)
                ? builds(operation) ? builds.get(operation) : null
                : facts.buildsItsResultFrom(operation);
        return built == null ? null : built.withArguments(DeclaredArgument::position);
    }

    /** Whether what {@code operation}, which the library writes, is stated to build is what its
     *  body builds. */
    private boolean builds(ValueName.Stdlib.Operation operation) {
        Boolean done = provedToBuild.get(operation);
        if (done != null) {
            return done;
        }
        BuiltFrom<DeclaredArgument> stating = builds.get(operation);
        if (stating == null) {
            return false;
        }
        List<Object> asking = List.of(operation, BuiltFrom.class);
        if (!underWay.add(asking)) {
            return false;   // a proof reading what it is proving: nothing settles it yet
        }
        boolean proved = elements.prove(operation,
                stating.withArguments(DeclaredArgument::position))
                instanceof LibraryProver.Outcome.Proved;
        underWay.remove(asking);
        provedToBuild.put(operation, proved);
        return proved;
    }

    /** How {@code observed} of {@code operation}, which the library writes, is settled. */
    BoundOperationFacts.Settled settle(ValueName.Stdlib.Operation operation,
                                       OperationLaw.Observed observed) {
        Map<OperationLaw.Observed, BoundOperationFacts.Settled> done =
                settled.computeIfAbsent(operation, _ -> new HashMap<>());
        BoundOperationFacts.Settled already = done.get(observed);
        if (already != null) {
            return already;
        }
        Stated what = stated.getOrDefault(operation, Map.of()).get(observed);
        if (what == null) {
            return null;
        }
        List<Object> asking = List.of(operation, observed);
        if (!underWay.add(asking)) {
            return null;   // a proof reading the law it is proving: nothing settles it yet
        }
        BoundOperationFacts.Settled settling = proved(operation, observed, what);
        underWay.remove(asking);
        done.put(observed, settling);
        return settling;
    }

    private BoundOperationFacts.Settled proved(ValueName.Stdlib.Operation operation,
                                               OperationLaw.Observed observed, Stated what) {
        if (what.closedAs() != null) {
            // A closing is what the body comes to on that side where the domain has no words for
            // it: a statement of nothing, which only words the domain lacks can leave unproved.
            OperationLaw<Integer> nothing = new OperationLaw.Observation<>(sideOf(observed),
                    new LawProposition.Always<>(true));
            // The body shows the domain has no words for the side by coming to a proposition it
            // has none for; the closing is taken only where that is the one it names or one it
            // is stated through.
            return switch (prover.prove(operation, new Lemma(nothing, what.carries()))) {
                case LibraryProver.Outcome.Unsaid(Unsayable why) when what.closedAs().standsOn(why)
                        && about(operation, what.closedAs()) ->
                        new BoundOperationFacts.Settled.Unsaid(what.closedAs());
                case LibraryProver.Outcome.Unsaid _ -> new BoundOperationFacts.Settled.Open(null,
                        new Unproved.DoesNotFollow(Unproved.Obligation.THE_STATEMENT));
                case LibraryProver.Outcome.Open(Unproved why) ->
                        new BoundOperationFacts.Settled.Open(null, why);
                case LibraryProver.Outcome.Proved _ -> new BoundOperationFacts.Settled.Open(null,
                        new Unproved.DoesNotFollow(Unproved.Obligation.THE_STATEMENT));
            };
        }
        return switch (prover.prove(operation, new Lemma(
                ByPlace.law(what.law(), DeclaredArgument::position), what.carries()))) {
            case LibraryProver.Outcome.Proved(var proof) -> new BoundOperationFacts.Settled.ByALaw(
                    what.law(), new BoundOperationFacts.Grounds.Proved(proof));
            case LibraryProver.Outcome.Unsaid(Unsayable why) ->
                    new BoundOperationFacts.Settled.Unsaid(why);
            case LibraryProver.Outcome.Open(Unproved why) ->
                    new BoundOperationFacts.Settled.Open(what.law(), why);
        };
    }

    /** Whether {@code operation}'s body answers a number standing as {@code bound} says, wherever
     *  what the bound is provided under holds. */
    private boolean bounds(ValueName.Stdlib.Operation operation,
                           ResultBound<DeclaredArgument> bound) {
        LinearForm<LawNumber<Integer>> against = bound.against() == null
                ? LinearForm.constant(ExactRatio.of(bound.offset()))
                : new LinearForm<>(ExactRatio.of(bound.offset()),
                        Map.of(numberAt(bound.against()), ExactRatio.ONE));
        LawProposition<Integer> where = switch (bound.provided()) {
            case ResultBound.Provided.Always<DeclaredArgument> _ -> new LawProposition.Always<>(true);
            case ResultBound.Provided.ConstantAboveZero<DeclaredArgument>(var argument) ->
                    new LawProposition.Compared<>(LinearForm.atom(numberAt(argument)), Rel.GT);
        };
        return prover.answers(operation, bound.rel(), against, where)
                instanceof LibraryProver.Outcome.Proved;
    }

    /** Whether {@code operation}'s body answers the number {@code one} says, of its arguments,
     *  wherever they stand as the case says. */
    private boolean answersInTheCase(ValueName.Stdlib.Operation operation,
                                     DefinitionCase<DeclaredArgument> one) {
        List<LawProposition<Integer>> given = new ArrayList<>();
        for (ArgumentsStand<DeclaredArgument> stand : one.given()) {
            switch (numbersOf(stand.left()).minus(numbersOf(stand.right()))) {
                case ExactAnswer.Held<LinearForm<LawNumber<Integer>>>(var held) ->
                        given.add(new LawProposition.Compared<>(held, stand.rel()));
                // A condition with no number is no condition the body can be held to.
                case ExactAnswer.Unheld<LinearForm<LawNumber<Integer>>> _ -> {
                    return false;
                }
            }
        }
        LawProposition<Integer> where = switch (given.size()) {
            case 0 -> new LawProposition.Always<>(true);
            case 1 -> given.getFirst();
            default -> new LawProposition.All<>(given);
        };
        return prover.answers(operation, Rel.EQ, numbersOf(one.answers()), where)
                instanceof LibraryProver.Outcome.Proved;
    }

    /** {@code form}, each argument it is written in as the number at its place. */
    private static LinearForm<LawNumber<Integer>> numbersOf(LinearForm<DeclaredArgument> form) {
        Map<LawNumber<Integer>, ExactRatio> numbers = new LinkedHashMap<>();
        form.coefs().forEach((argument, weight) -> numbers.put(numberAt(argument), weight));
        return new LinearForm<>(form.constant(), numbers);
    }

    private static LawNumber<Integer> numberAt(DeclaredArgument argument) {
        return new LawNumber.AnArgument<>(argument.position());
    }

    /** The side of an answer {@code observed} is about; a closing is of a side, never of a size. */
    private static AnswerAspect sideOf(OperationLaw.Observed observed) {
        return switch (observed) {
            case TRUTH -> AnswerAspect.TRUTH;
            case EMPTINESS -> AnswerAspect.EMPTINESS;
            case PRESENCE -> AnswerAspect.PRESENCE;
            case SIZE -> throw new IllegalStateException("a size is closed, which only a side is");
        };
    }

    /** How a side of {@code operation} is settled, as a proof reads it. */
    private Library.Settled forAProof(ValueName.Stdlib.Operation operation,
                                      OperationLaw.Observed observed) {
        BoundOperationFacts.Settled settling = stdlib.helpers().containsKey(operation)
                ? settle(operation, observed)
                : kernels.getOrDefault(operation, Map.of()).get(observed);
        return switch (settling) {
            case null -> null;
            case BoundOperationFacts.Settled.ByALaw(var law, var _) ->
                    new Library.Settled.ByALaw(ByPlace.law(law, DeclaredArgument::position));
            case BoundOperationFacts.Settled.Unsaid(Unsayable why) -> new Library.Settled.Unsaid(why);
            case BoundOperationFacts.Settled.Open(var _, Unproved why) ->
                    new Library.Settled.Open(why);
        };
    }
}
