package souther.compiler.examples;

import souther.compiler.observe.RowIdentity;

/**
 * The address an application writes a row down as, to tie world state to it.
 *
 * <p>Two things it must be, and the type closes both. It holds a {@link RowIdentity.Named}, so a key
 * for a row that has no name cannot be written — #718 put the namespace on the behavior and this
 * finishes that decision. And it is made only by {@link BoundExamples#row(String, String)}, so a key
 * naming a row nothing answers to cannot be written either. Left as a record, its canonical
 * constructor would be public and a name nothing answers to would be written straight past the
 * resolution: {@link #is} would answer {@code false} for every row and the setup guarded by it would
 * silently never run, which is the failure this whole type exists to prevent.
 *
 * <p>Not what {@link BoundExamples#evaluate} takes. A row written without a name still runs — it
 * needs an address to be associated with something outside the file, not to be evaluated — and
 * keyed evaluation would silently drop every unnamed row of the behavior.
 *
 * <p>Made through {@link BoundExamples#row(String, String)} so a name nothing answers to fails where
 * it is resolved, rather than as setup that silently never runs.
 */
public final class RowKey {

    private final BoundExamples of;
    private final String behavior;
    private final RowIdentity.Named row;

    RowKey(BoundExamples of, String behavior, RowIdentity.Named row) {
        this.of = of;
        this.behavior = behavior;
        this.row = row;
    }

    /** The behavior whose row this addresses. */
    public String behavior() {
        return behavior;
    }

    /** What the row names itself. */
    public RowIdentity.Named row() {
        return row;
    }

    /** The name the row was written with. */
    public String name() {
        return row.name();
    }

    /**
     * Whether {@code enumerated} is the row this addresses.
     *
     * <p>A row of another enumeration is refused rather than answered {@code false}. Answering would
     * make a key written against one binding quietly match nothing in another, which is the setup
     * that never runs, moved one call along.
     */
    public boolean is(RecordedRow enumerated) {
        if (enumerated == null) {
            throw new IllegalArgumentException("a key is asked about a row");
        }
        if (enumerated.enumeratedBy() != of) {
            throw new IllegalArgumentException("this key was resolved against another enumeration,"
                    + " so what it addresses is not among these rows");
        }
        return behavior.equals(enumerated.behavior()) && row.equals(enumerated.identity());
    }

    @Override
    public String toString() {
        return behavior + " " + row.shown();
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof RowKey key && of == key.of
                && behavior.equals(key.behavior) && row.equals(key.row);
    }

    @Override
    public int hashCode() {
        return System.identityHashCode(of) * 31 + behavior.hashCode() * 31 + row.hashCode();
    }
}
