package souther.compiler.proof;

import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.ClosurePositions;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.Unsayable;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;

/**
 * What a proof about one of the library's operations may take of the others, handed over by
 * whoever is settling them all.
 *
 * <p>A proof reads another operation's law where the body calls it, and that law is an axiom of a
 * kernel or one proved in turn; which, and in what order, is the settling's to know. So a proof
 * asks here and never reaches for a table of its own, and a law it is handed is one already settled
 * — never a declaration standing in for one.
 */
public interface Library {

    /** The library itself, whose bodies are read. */
    Stdlib stdlib();

    /** How {@code operation}'s answer on {@code observed} is settled, or null where it is not. */
    Settled settled(ValueName.Stdlib.Operation operation, OperationLaw.Observed observed);

    /**
     * The number {@code operation} answers, as a number of its arguments read by place — where it
     * answers a number taken of one of them or the sum or difference of two — or null where it
     * answers none such.
     */
    LinearForm<LawNumber<Integer>> answersTheNumber(ValueName.Stdlib.Operation operation);

    /** What {@code operation}'s answer lists of one of its arguments, or null where nothing. */
    AppliedClosures.Listing listing(ValueName.Stdlib.Operation operation);

    /** Where {@code operation}'s signature puts a closure beside a container, or null. */
    ClosurePositions positions(ValueName.Stdlib.Operation operation);

    /**
     * What is stated of {@code operation}'s answer beside what other kernels answer on its
     * arguments — that a key a map holds is one only where the map holds something, how many an
     * insert answers against whether the key was there — over its arguments by place and any value,
     * each holding wherever the operation answers. Axioms of a kernel, held to what it computes.
     */
    List<LawProposition<Slot>> relations(ValueName.Stdlib.Operation operation);

    /** The types of {@code operation}'s arguments, in order. */
    default List<Type> takes(ValueName.Stdlib.Operation operation) {
        return stdlib().entry(operation).signature().params();
    }

    /** How one side of an operation's answer is settled. */
    sealed interface Settled {

        /** By {@code law}, over the arguments named by their places. */
        record ByALaw(OperationLaw<Integer> law) implements Settled {}

        /** By the proposition the domain has no words for. */
        record Unsaid(Unsayable why) implements Settled {}

        /** By nothing yet: what was stated of it is not proved, for {@code why}. */
        record Open(Unproved why) implements Settled {}
    }
}
