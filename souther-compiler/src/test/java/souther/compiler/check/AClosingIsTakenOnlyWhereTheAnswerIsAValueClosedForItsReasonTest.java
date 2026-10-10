package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.proof.Library;
import souther.compiler.proof.LibraryProver;
import souther.compiler.proof.Unproved;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.Unsayable;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A closing of an operation the library writes is taken where its body answers, in every case,
 * what an operation answers whose same observation is closed for the same reason — and nowhere a
 * proof merely met such a value.
 *
 * <p>Asked of the library's own bodies with how the operations they call are settled handed in,
 * so what is held is the rule for a closing and not which closings the library happens to have:
 * every closing it declares today is of a kernel.
 */
class AClosingIsTakenOnlyWhereTheAnswerIsAValueClosedForItsReasonTest {

    private static final ValueName.Stdlib.Operation LIST_CONCAT =
            new ValueName.Stdlib.Operation("List", "concat");
    private static final ValueName.Stdlib.Operation LIST_IS_EMPTY =
            new ValueName.Stdlib.Operation("List", "isEmpty");

    private static final Unsayable WHY = Unsayable.WHICH_CHARACTERS_ARE_WHITESPACE;
    private static final Unsayable ANOTHER = Unsayable.A_STRING_INSIDE_ANOTHER;

    /** A prover over the library, with every observation of every operation closed for
     *  {@code why}. */
    private static LibraryProver everythingClosedFor(Unsayable why) {
        Library library = new LibraryUnderProof(DefaultStdlib.get(),
                DefaultBoundOperationFacts.get(),
                (operation, observed) -> new Library.Settled.Unsaid(why),
                operation -> null, operation -> List.of());
        return new LibraryProver(library, Set.of());
    }

    /** {@code List.concat} answers what a walk answers, so how many it holds is that walk's. */
    @Test
    void anAnswerThatIsAValueClosedForTheReasonIsClosedForIt() {
        assertInstanceOf(LibraryProver.Outcome.Proved.class, everythingClosedFor(WHY)
                .closes(LIST_CONCAT, OperationLaw.Observed.SIZE, WHY));
    }

    /** The same answer closed for another reason closes nothing for this one. */
    @Test
    void anAnswerClosedForAnotherReasonIsNoClosingForThisOne() {
        assertEquals(new LibraryProver.Outcome.Open(new Unproved.DoesNotFollow(
                        Unproved.Obligation.THE_CASES)),
                everythingClosedFor(ANOTHER).closes(LIST_CONCAT, OperationLaw.Observed.SIZE,
                        WHY));
    }

    /**
     * {@code List.isEmpty} compares a length its body reads with nought: the value closed for the
     * reason is met on the way, and the answer is a comparison, which may have words — so nothing
     * is closed.
     */
    @Test
    void aValueClosedForTheReasonMetOnTheWayClosesNothing() {
        assertEquals(new LibraryProver.Outcome.Open(new Unproved.DoesNotFollow(
                        Unproved.Obligation.THE_CASES)),
                everythingClosedFor(WHY).closes(LIST_IS_EMPTY, OperationLaw.Observed.TRUTH,
                        WHY));
    }
}
