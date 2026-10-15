package souther.compiler.query;

import souther.compiler.coverage.SiteNumbering;
import souther.compiler.observe.RowOutcome;
import souther.compiler.partition.ObservedInputs;

import java.util.Objects;
import java.util.Optional;

/**
 * A written row as a measure reads it, and what it is as a witness of whatever it is found to cover.
 *
 * <p>Two things and not one. {@link ObservedInputs} is what is measured, and it is not a row: the
 * generator hands candidates of its own to the same questions, and a candidate is nobody's witness.
 * So what a written row is as evidence travels beside its values rather than inside them, and only a
 * measure over written rows has it to carry.
 *
 * @param observed the values the row holds and what running it recorded
 * @param by       what the row is as a witness
 */
public record WitnessedRow(ObservedInputs observed, RowWitnesses by) {

    public WitnessedRow {
        Objects.requireNonNull(observed, "a witnessed row is some row's values");
        Objects.requireNonNull(by, "a witnessed row says what it is as a witness");
    }

    /** {@code row} read under {@code numbering}, as {@link ObservedInputs#of} reads it. */
    public static WitnessedRow of(RowOutcome row, Optional<SiteNumbering> numbering) {
        return new WitnessedRow(ObservedInputs.of(row, numbering), RowWitnesses.of(row));
    }
}
