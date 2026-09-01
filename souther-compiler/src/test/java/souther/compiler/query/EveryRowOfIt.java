package souther.compiler.query;

/**
 * A composition rendered as though every row of it were offered, for a test with no store.
 *
 * <p>What is offered is what is left once each row has been asked what it would settle, and asking
 * takes a store: values to build the row through and something to run it against. A test that
 * builds its fillings by hand has neither, and what it is testing is not which rows go out but what
 * the block says beside them.
 *
 * <p>Here rather than beside {@link Composition}, and in the tests rather than in what ships. A
 * production caller has a store, and one that came through something like this would be choosing to
 * skip the question — which is the way back to a renderer printing rows nobody chose.
 */
public final class EveryRowOfIt {

    /** The offering that keeps every row of {@code composed} and says nothing is answered, which is
     *  what not having asked means. */
    public static Offering offered(Composition composed) {
        return composed.keeping(
                composed.rowsByBehavior().values().stream().flatMap(java.util.List::stream)
                        .map(OfferedRow::key)
                        .collect(java.util.stream.Collectors.toCollection(
                                java.util.LinkedHashSet::new)),
                java.util.Set.of());
    }

    private EveryRowOfIt() {}
}
