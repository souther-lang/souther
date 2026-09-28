package souther.compiler.partition;

/** Asking a quantity about a row, for a test that holds one. */
public final class QuantityFixtures {

    private QuantityFixtures() {
    }

    /**
     * Where {@code observation}'s row stands at {@code where} on {@code quantity}.
     *
     * <p>The two steps a measure takes apart, taken together here. A measure reads a row once and
     * asks about it as many times as there are readings and criteria, which is why the quantity
     * takes a reading rather than a row; a test holding one row and asking one question about it
     * has nothing to keep the reading for.
     */
    public static BorderQuantity.Stands stands(BorderQuantity quantity, Criterion where,
                                               BorderQuantity.Observation observation) {
        return quantity.standsAt(where, quantity.read(observation));
    }
}
