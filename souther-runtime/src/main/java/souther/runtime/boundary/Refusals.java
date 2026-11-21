package souther.runtime.boundary;

import org.jspecify.annotations.Nullable;
import souther.runtime.PersistentVector;

import java.util.List;

/**
 * Everything a decode refused, in the order it was read: one refusal for each value that could not
 * be read, so independent fields are all reported (spec {@code [#case-propagation]}). Never empty.
 *
 * <p>Held in a persistent vector, so a list whose every element is refused gathers its refusals one
 * by one without copying what it gathered so far.
 */
public final class Refusals {

    private final PersistentVector<Refusal> refusals;

    private Refusals(PersistentVector<Refusal> refusals) {
        this.refusals = refusals;
    }

    /** One refusal. */
    public static Refusals of(Refusal refusal) {
        return new Refusals(PersistentVector.ofSingle(refusal));
    }

    /** These refusals and then {@code more}. */
    public Refusals and(Refusals more) {
        PersistentVector<Refusal> all = refusals;
        for (Refusal each : more.refusals) {
            all = all.append(each);
        }
        return new Refusals(all);
    }

    /** The refusals, in the order they were read. */
    public List<Refusal> asList() {
        return refusals;
    }

    @Override
    public boolean equals(@Nullable Object o) {
        return o instanceof Refusals other && refusals.equals(other.refusals);
    }

    @Override
    public int hashCode() {
        return refusals.hashCode();
    }

    @Override
    public String toString() {
        return refusals.toString();
    }
}
