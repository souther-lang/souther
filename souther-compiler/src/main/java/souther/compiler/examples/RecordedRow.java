package souther.compiler.examples;

import souther.compiler.ast.Hir;
import souther.compiler.diag.SourcePos;
import souther.compiler.observe.RowIdentity;

/**
 * One row an enumeration made runnable, as the thing that runs it takes it.
 *
 * <p>A handle and not an address. It belongs to the enumeration that made it and is refused by any
 * other, which is what keeps a row of one binding from being run by another; what an application
 * writes down to tie world state to a row is {@link RowKey}, and the two are separate because only
 * one of them can be written for a row that has no name.
 *
 * <p>What it shows is the row's own name, or which of its behavior's rows it is where the row was
 * written without one. That is for a report and for naming a generated test, and is not what
 * anything keys on.
 */
public final class RecordedRow {

    private final BoundExamples of;
    private final String behavior;
    private final Hir.ExampleRow row;

    RecordedRow(BoundExamples of, String behavior, Hir.ExampleRow row) {
        this.of = of;
        this.behavior = behavior;
        this.row = row;
    }

    /** The behavior this is a row of. */
    public String behavior() {
        return behavior;
    }

    /** What the row names itself. */
    public RowIdentity identity() {
        return row.identity();
    }

    /** What a report writes to say which row this is. */
    public String shown() {
        return identity().shown();
    }

    /**
     * Where the row is written.
     *
     * <p>Needed beside the name rather than instead of it. An unnamed row is shown as which of its
     * behavior's rows it is <em>in its own source</em>, so a behavior exampled in a module and in an
     * attached file has a {@code #1} in each — what tells those apart is the source, and a consumer
     * naming a generated test after {@link #shown()} alone would name two of them the same.
     */
    public SourcePos at() {
        return row.pos();
    }

    @Override
    public String toString() {
        return behavior + " " + shown();
    }

    /** The enumeration this came from, so one binding does not run another's row. */
    BoundExamples enumeratedBy() {
        return of;
    }

    Hir.ExampleRow written() {
        return row;
    }
}
