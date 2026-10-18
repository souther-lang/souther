package souther.compiler.core;

import souther.compiler.types.BindingId;

import java.util.Objects;
import java.util.Optional;

/**
 * An arm of a match as the tree being read has it, told from another by the name it binds.
 *
 * <p>Not by what is written in it, and not by which arm of which match the source wrote. A helper
 * expanded at two places is two trees, each with its own arm of the one source match, and each
 * binds its own name; a condition on the way to a comparison in one is no condition of the other.
 * The source's name for the arm ({@code WrittenCondition.ForkArm}) is what a report is placed
 * under, and is the same for both.
 *
 * <p>A value, since it is held in answers that are compared by what they hold, and a name of the
 * tree read is the same on every reading of it. An arm that binds nothing has none.
 *
 * @param binder the name the arm binds
 */
public record EnteredArm(BindingId binder) {

    public EnteredArm {
        Objects.requireNonNull(binder, "an arm entered is told by the name it binds");
    }

    /** The arm {@code arm} of the tree being read, or none where it binds no name. */
    public static Optional<EnteredArm> of(Core.Case arm) {
        return arm.binder() == null || arm.binder().binding() == null ? Optional.empty()
                : Optional.of(new EnteredArm(arm.binder().binding()));
    }
}
