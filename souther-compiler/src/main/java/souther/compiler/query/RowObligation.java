package souther.compiler.query;

import souther.compiler.diag.SourcePos;
import souther.compiler.observe.RowRef;
import souther.compiler.partition.ObligationIdentity;

import java.util.Objects;

/**
 * One row an author wrote, and whether the answer it owes is written.
 *
 * <p>The entry of the row account. What a document publishes, what a build refuses over and where a
 * reader is sent are projections of a list of these, so no two surfaces can disagree about one row.
 *
 * <p>Read off the text and not off a run. Whether a row's answer is owed is settled where the row
 * was read and is true whatever becomes of the evaluation, so this account stands for a behavior
 * whose rows nobody ran — which is why it is not one of the things a measurement can go without.
 *
 * @param at where the row is written, which is where a reader is sent whichever way it stands.
 *           Not where the answer goes: {@link souther.compiler.ast.Hir.Expected} holds that, and a
 *           reader told to write an answer is told about the row it belongs to
 */
public record RowObligation(RowRef rowRef, SourcePos at, RowDisposition disposition) {

    public RowObligation {
        Objects.requireNonNull(rowRef, "an entry of the row account is about some row");
        Objects.requireNonNull(at, "a row is written somewhere");
        Objects.requireNonNull(disposition, "an entry says where it stands");
    }

    /** What tells this row from every other, in the shape its account keeps. */
    public ObligationIdentity obligationIdentity() {
        return new ObligationIdentity.OfARow(rowRef);
    }
}
