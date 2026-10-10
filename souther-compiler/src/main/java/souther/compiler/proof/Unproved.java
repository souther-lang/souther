package souther.compiler.proof;

import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.Unsayable;
import souther.compiler.types.ValueName;

/**
 * Why a statement about one of the library's operations is not proved against its body.
 *
 * <p>Each is about what this proving can do and not about what the domain can say: a statement the
 * domain has no words for is closed with the words it lacks instead ({@code semantics.Unsayable}).
 * One of these leaves the statement an open obligation, which nothing takes as a law.
 */
public sealed interface Unproved {

    /** The body holds something no rule here reads. */
    record ReadShort(LibraryTerm.Unwritten what) implements Unproved {}

    /** The body calls {@code operation}, and nothing settles {@code observed} of its answer. */
    record NothingSettles(ValueName.Stdlib.Operation operation, OperationLaw.Observed observed)
            implements Unproved {}

    /** The body calls {@code operation}, whose {@code observed} is itself not proved. */
    record OpenBelow(ValueName.Stdlib.Operation operation, OperationLaw.Observed observed)
            implements Unproved {}

    /**
     * The statement turns on what the body calls answering something the domain has no words for,
     * for {@code why}. Not proved, and not a closing either: the statement is in words the domain
     * has, and what lacks them is a value the proof needed to read, which says nothing of whether
     * the statement holds.
     */
    record TurnsOnWhatIsNotSaid(Unsayable why) implements Unproved {}

    /** What the body comes to is a statement about more than the operation's own arguments. */
    record NotOverItsArguments() implements Unproved {}

    /** {@code which} does not follow. */
    record DoesNotFollow(Obligation which) implements Unproved {}

    /** The body walks a list and no statement of what the walk carries was given. */
    record NoInvariantGiven() implements Unproved {}

    /** What a proof has to show. */
    enum Obligation {
        /** That the statement is what the body comes to. */
        THE_STATEMENT,
        /** That what a walk carries is stated of where it starts. */
        THE_SEED,
        /** That a step from where the statement of a walk holds ends where it holds. */
        A_STEP,
        /** That every case the body answers by is one the statement names. */
        THE_CASES,
        /** That every element of the answer came from where the statement says. */
        WHERE_ITS_ELEMENTS_CAME_FROM,
        /** That the answer holds as many elements as the statement says. */
        HOW_MANY_IT_HOLDS
    }
}
