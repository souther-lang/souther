package souther.compiler.execute;

import souther.compiler.ast.Hir;
import souther.compiler.check.Sig;
import souther.compiler.coverage.Observation;

import java.util.List;
import java.util.Optional;

/**
 * A way to run rows nobody wrote and see where they went.
 *
 * <p>What a search needs and an evaluation does not. A row composed to fill a gap has no expected
 * value to be held to; what is wanted of it is which arms it reached, so that a candidate can be
 * offered on the strength of what it actually covers rather than on what it looks like it would.
 *
 * <p>A way to ask, for the reason {@link BoundaryValues} is one: the classes the rows are run
 * against are settled once and every candidate goes through the same ones.
 */
@FunctionalInterface
public interface RowTrials {

    /** A way to run rows of {@code behavior}. */
    OfBehavior forBehavior(String behavior, Sig sig);

    /**
     * A way to run one row's inputs and see what it did.
     *
     * <p>Empty is an ordinary answer and not a failure. Nothing having run a row leaves every
     * combination as untried as it was; a row that ran and reached nothing is a row that missed, and
     * the two must not come back as one value.
     */
    @FunctionalInterface
    interface OfBehavior {

        /** What running {@code inputs} was seen doing, or empty where nothing could run them. */
        Optional<Observation> run(List<Hir.Expr> inputs);
    }
}
