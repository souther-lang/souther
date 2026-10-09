package souther.compiler.check;

import souther.compiler.numeric.LinearForm;
import souther.compiler.proof.AppliedClosures;
import souther.compiler.proof.Library;
import souther.compiler.proof.Slot;
import souther.compiler.semantics.ClosurePositions;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.TakenAs;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.function.BiFunction;

/**
 * The library as a proof about one of its operations may take it: the kernels' facts as they are
 * bound, and every other operation's laws as whoever is settling them all says.
 *
 * <p>How an operation is settled is handed in ({@code settling}) rather than looked up here, since
 * an operation the library writes in the language is settled by proving it, and which proofs are
 * done and which are under way is the settling's to know.
 */
final class LibraryUnderProof implements Library {

    private final Stdlib stdlib;
    private final BoundOperationFacts facts;
    private final BiFunction<ValueName.Stdlib.Operation, OperationLaw.Observed, Settled> settling;

    LibraryUnderProof(Stdlib stdlib, BoundOperationFacts facts,
                      BiFunction<ValueName.Stdlib.Operation, OperationLaw.Observed, Settled>
                              settling) {
        this.stdlib = stdlib;
        this.facts = facts;
        this.settling = settling;
    }

    @Override
    public Stdlib stdlib() {
        return stdlib;
    }

    @Override
    public Settled settled(ValueName.Stdlib.Operation operation, OperationLaw.Observed observed) {
        return settling.apply(operation, observed);
    }

    /** The number an operation answers where it is declared to be how many one argument holds. */
    @Override
    public LinearForm<LawNumber<Integer>> answersTheNumber(ValueName.Stdlib.Operation operation) {
        BoundOperationFact.AnswersANumberTakenOfAValueItIsGiven taken =
                facts.numberTakenOf(operation);
        return taken != null && taken.how() instanceof TakenAs.HowManyItHolds
                ? LinearForm.atom(new LawNumber.SizeOf<>(
                        new LawSubject.Argument<>(taken.of().position())))
                : null;
    }

    @Override
    public AppliedClosures.Listing listing(ValueName.Stdlib.Operation operation) {
        return Combinators.listing(stdlib, facts, operation);
    }

    @Override
    public ClosurePositions positions(ValueName.Stdlib.Operation operation) {
        return Combinators.positionsOf(operation);
    }

    @Override
    public List<LawProposition<Slot>> relations(ValueName.Stdlib.Operation operation) {
        return facts.relationsOf(operation);
    }
}
