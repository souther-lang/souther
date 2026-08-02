package souther.runtime;

/** A case of {@link RoundingMode}. A unit data: the only value is {@link #INSTANCE}. */
public record FLOOR() implements RoundingMode {

    public static final FLOOR INSTANCE = new FLOOR();

    // The overrides pin the shape generated unit data has: equality by case, a stable hash,
    // and the record-style text form.
    @Override
    public boolean equals(Object o) {
        return o instanceof FLOOR;
    }

    @Override
    public int hashCode() {
        return 1;
    }

    @Override
    public String toString() {
        return "FLOOR[]";
    }
}
