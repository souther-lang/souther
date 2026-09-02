package souther.compiler.query;

import souther.compiler.ast.Hir;
import souther.compiler.inputs.InputDomain;

import java.util.Objects;

/**
 * Where a measure of one behavior reads what that behavior takes.
 *
 * <p>Two places and not two outcomes. A declared behavior takes an input of its own and it is read
 * here; a {@code >->} composition takes what its first stage takes and is measured there. Both are
 * facts about the behavior, settled by its declaration, and neither is a measurement that could not
 * be made — what this compilation failed to work out is {@link BoundaryForMeasurement.NotDerived}
 * and lives on the other side of the boundary.
 *
 * <p>Which is why this is inside {@link BoundaryForMeasurement.Derived} rather than beside it. Held
 * as a third state of the boundary, a reader asking whether the boundary was worked out would write
 * {@code instanceof Derived} and leave a composition out of an answer it belongs in — the two are
 * different questions, and only one of them is about this compilation.
 */
public sealed interface InputForMeasurement {

    /**
     * The behavior's own input, as it was read.
     *
     * <p>The declaration and the reading together, because the reading is of that declaration and
     * of no other. Handed the reading alone, a reader that needed to know whose positions these are
     * would go back to the behavior it started from and pair the two a second time — and two
     * behaviors with a parameter spelled the same way is all it takes for the second pairing to
     * differ from the first.
     *
     * @param spec the declaration these positions were read from, which is what says the behavior
     *             has an input of its own at all
     */
    record Local(Hir.SpecBehavior spec, InputDomain domain) implements InputForMeasurement {

        public Local {
            Objects.requireNonNull(spec, "a local input is read from a declaration");
            Objects.requireNonNull(domain, "a local input is an input that was read");
        }
    }

    /**
     * The behavior takes what its first stage takes, so what it takes is measured there.
     *
     * <p>No reading here and none owed: a composition names its stages and each of them is a
     * behavior of its own with its own positions. Said as what it is rather than as an input with
     * no positions, which is what a behavior the model divides nowhere comes back with.
     */
    enum AtStages implements InputForMeasurement {
        INSTANCE
    }
}
