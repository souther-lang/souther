package souther.compiler.check;

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
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.ArgumentsStand;
import souther.compiler.semantics.DefinitionCase;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.ResultBound;
import souther.compiler.semantics.Unsayable;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
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
    private final Map<ValueName, Map<OperationLaw.Observed, BoundOperationFacts.Settled>> kernels;
    private final Map<ValueName.Stdlib.Operation, Map<OperationLaw.Observed, Stated>> stated;
    private final Map<ValueName.Stdlib.Operation, Map<OperationLaw.Observed,
            BoundOperationFacts.Settled>> settled = new HashMap<>();
    private final Set<List<Object>> underWay = new HashSet<>();
    private final LibraryProver prover;

    ProvingTheLibrary(Stdlib stdlib, BoundOperationFacts facts,
                      Map<ValueName, Map<OperationLaw.Observed, BoundOperationFacts.Settled>> kernels,
                      Map<ValueName.Stdlib.Operation, Map<OperationLaw.Observed, Stated>> stated) {
        this.stdlib = stdlib;
        this.kernels = kernels;
        this.stated = stated;
        Library library = new LibraryUnderProof(stdlib, facts, this::forAProof);
        Set<ValueName.Stdlib.Operation> walks = new LinkedHashSet<>(WalksFromASeed.of(stdlib,
                AppliedClosures.of(stdlib, Combinators.kernelsIn(stdlib),
                        operation -> Combinators.listing(stdlib, facts, operation),
                        Combinators::positionsOf)).keySet());
        walks.remove(stdlib.walk().operation());
        this.prover = new LibraryProver(library, walks);
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
                case LibraryProver.Outcome.Unsaid(Unsayable why) when what.closedAs().standsOn(why) ->
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
    boolean bounds(ValueName.Stdlib.Operation operation, ResultBound<DeclaredArgument> bound) {
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

    /** Whether {@code operation}'s body answers the argument {@code one} names wherever its
     *  arguments stand as the case says. */
    boolean answersInTheCase(ValueName.Stdlib.Operation operation,
                             DefinitionCase<DeclaredArgument> one) {
        List<LawProposition<Integer>> given = new ArrayList<>();
        for (ArgumentsStand<DeclaredArgument> stand : one.given()) {
            given.add(new LawProposition.Compared<>(
                    LinearForm.difference(numberAt(stand.left()), numberAt(stand.right())),
                    stand.rel()));
        }
        LawProposition<Integer> where = switch (given.size()) {
            case 0 -> new LawProposition.Always<>(true);
            case 1 -> given.getFirst();
            default -> new LawProposition.All<>(given);
        };
        return prover.answers(operation, Rel.EQ, LinearForm.atom(numberAt(one.answers())), where)
                instanceof LibraryProver.Outcome.Proved;
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
