package souther.compiler.partition;

/**
 * Which composed row, within one run of the generator and nowhere else.
 *
 * <p>An identity and not a position. One set of values answers as many obligations as it happens to
 * — a row for a class of a position that also takes an arm of the body is one line in the file —
 * and what says so is that both obligations name this. Read as an index into the rows a run offers,
 * the identity would move with whatever the offer was ordered by, and two obligations answered by
 * one row would come apart the day the order changed.
 *
 * <p>Opaque outside the run that made it. Nothing compares one of these with an id from another
 * generation, and nothing reads the number for anything but telling one row from the next.
 */
public record RowId(int value) {

    public RowId {
        if (value < 0) {
            throw new IllegalArgumentException("a row is numbered from nought: " + value);
        }
    }

    @Override
    public String toString() {
        return "row " + value;
    }
}
