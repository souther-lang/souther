package souther.compiler.proof;

import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Set;

/**
 * How a statement about an operation the library writes in the language was proved against its
 * body: by which rule, and on which other operations' laws.
 *
 * <p>Each other law named is settled on its own — an axiom of a kernel, or proved in turn — so a
 * proof together with the proofs of what it names walks back to axioms and nothing else.
 */
public sealed interface Proof {

    /** The operation the statement is about. */
    ValueName.Stdlib.Operation operation();

    /** The laws of other operations the proof took. */
    Set<Used> used();

    /** What the body comes to, case by case, read through the laws of what it calls. */
    record ByTheBody(ValueName.Stdlib.Operation operation, Set<Used> used) implements Proof {

        public ByTheBody {
            used = Set.copyOf(used);
        }
    }

    /**
     * What a walk in the body carries, shown of where it starts and of every step from where it
     * holds, and read where the walk ends.
     */
    record ByInduction(ValueName.Stdlib.Operation operation,
                       List<LawProposition<Slot>> carries, Set<Used> used) implements Proof {

        public ByInduction {
            carries = List.copyOf(carries);
            used = Set.copyOf(used);
        }
    }

    /**
     * Where every element of the answer came from, read off what the body builds it with: a walk
     * putting in at most one value for each element it is handed, an argument as it stands, or what
     * another operation is settled to build.
     */
    record ByWhatItsBodyBuilds(ValueName.Stdlib.Operation operation, Set<Used> used)
            implements Proof {

        public ByWhatItsBodyBuilds {
            used = Set.copyOf(used);
        }
    }

    /** What a proof took of {@code operation}. */
    record Used(ValueName.Stdlib.Operation operation, Taken taken) {

        static Used law(ValueName.Stdlib.Operation operation, OperationLaw.Observed observed) {
            return new Used(operation, switch (observed) {
                case TRUTH -> Taken.ITS_TRUTH;
                case EMPTINESS -> Taken.WHETHER_IT_HOLDS_SOMETHING;
                case PRESENCE -> Taken.WHETHER_IT_HOLDS_A_VALUE;
                case SIZE -> Taken.HOW_MANY_IT_HOLDS;
            });
        }
    }

    /** Which statement of another operation a proof took. */
    enum Taken {
        ITS_TRUTH,
        WHETHER_IT_HOLDS_SOMETHING,
        WHETHER_IT_HOLDS_A_VALUE,
        HOW_MANY_IT_HOLDS,
        /** The number it answers, as a number of its arguments. */
        THE_NUMBER_IT_ANSWERS,
        /** That its answer lists every element of an argument, each once. */
        WHAT_IT_LISTS,
        /** Where the elements of its answer came from, and how many there are. */
        WHAT_IT_BUILDS,
        /** That its answer is a container with one value put in. */
        WHAT_IT_PUTS_IN
    }
}
