package souther.compiler.partition;

import souther.compiler.types.ModelOccurrence;

import java.util.Objects;

/**
 * A choice the values of a condition are made through.
 *
 * @param construct the choice, in the copy of the model it stands in
 * @param arms      how many of its arms answer something
 */
public record AChoiceReadThrough(ModelOccurrence construct, int arms) {

    public AChoiceReadThrough {
        Objects.requireNonNull(construct, "a choice is written somewhere");
    }

    /**
     * At most how many readings of a condition one reading of it becomes at this choice: one on
     * each arm, and one of what decides between them, which may be made through the choices after
     * it as the condition is.
     */
    public long readings() {
        return arms + 1L;
    }
}
