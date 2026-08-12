package souther.runtime;

import org.jspecify.annotations.Nullable;

/** A case of {@link RoundingMode}. A unit data: the only value is {@link #INSTANCE}. */
public record UP() implements RoundingMode {

    public static final UP INSTANCE = new UP();

    // The overrides pin the shape generated unit data has: equality by case, a stable hash,
    // and the record-style text form.
    @Override
    public boolean equals(@Nullable Object o) {
        return o instanceof UP;
    }

    @Override
    public int hashCode() {
        return 1;
    }

    @Override
    public String toString() {
        return "UP[]";
    }
}
