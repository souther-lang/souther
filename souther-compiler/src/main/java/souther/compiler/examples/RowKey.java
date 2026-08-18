package souther.compiler.examples;

import souther.compiler.observe.RowIdentity;

/**
 * The address an application writes a row down as, to tie world state to it.
 *
 * <p>Holds a {@link RowIdentity.Named}, so a key for a row that has no name cannot be written.
 * {@code RowKey(String, String)} with a checking factory would leave that case representable and
 * refuse it at run time; #718 put the namespace on the behavior, and this finishes that decision by
 * making the unnameable case unwritable.
 *
 * <p>Not what {@link BoundExamples#evaluate} takes. A row written without a name still runs — it
 * needs an address to be associated with something outside the file, not to be evaluated — and
 * keyed evaluation would silently drop every unnamed row of the behavior.
 *
 * <p>Made through {@link BoundExamples#row(String, String)} so a name nothing answers to fails where
 * it is resolved, rather than as setup that silently never runs.
 */
public record RowKey(String behavior, RowIdentity.Named row) {

    public RowKey {
        if (behavior == null || behavior.isBlank()) {
            throw new IllegalArgumentException("a key names the behavior whose row it is");
        }
        if (row == null) {
            throw new IllegalArgumentException("a key names a row that has a name");
        }
    }

    /** Whether {@code enumerated} is the row this addresses. */
    public boolean is(RecordedRow enumerated) {
        return enumerated != null
                && behavior.equals(enumerated.behavior())
                && row.equals(enumerated.identity());
    }

    /** The name the row was written with. */
    public String name() {
        return row.name();
    }
}
