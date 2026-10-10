package souther.compiler.check;

import souther.compiler.semantics.OperationLaw;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Map;

/**
 * What is proved of the operations the library writes, as settling the facts asks it: how each
 * observation stated of one is settled, and whether each other fact stated of one holds of its
 * body.
 *
 * <p>Two ways to come by it and one answer. Proved here, each against its body
 * ({@link ProvingTheLibrary}), or read off what proving them here came to when this compiler was
 * built ({@link LibraryProofsAsBuilt}): the build writes the second from the first, and a test holds
 * the two to one another.
 */
interface LibraryProofs {

    /** How {@code observed} of what {@code operation} answers is settled, or null where nothing
     *  stated of it settles it. */
    BoundOperationFacts.Settled settle(ValueName.Stdlib.Operation operation,
                                       OperationLaw.Observed observed);

    /** Whether {@code fact}, stated of an operation the library writes, holds of its body. */
    boolean proves(BoundOperationFact fact);

    /** How the proofs of one set of facts are come by. */
    interface Source {

        /**
         * The proofs of what {@code stated} and {@code awaiting} say of the operations the library
         * writes, beside {@code settled}, what is settled of the kernels.
         */
        LibraryProofs over(Stdlib stdlib, BoundOperationFacts facts,
                           Map<ValueName, Map<OperationLaw.Observed, BoundOperationFacts.Settled>>
                                   settled,
                           Map<ValueName.Stdlib.Operation,
                                   Map<OperationLaw.Observed, ProvingTheLibrary.Stated>> stated,
                           List<BoundOperationFact> awaiting);
    }

    /** Each proved here, against its body. */
    Source PROVING = ProvingTheLibrary::new;
}
