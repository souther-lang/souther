package souther.compiler.partition;

/**
 * What a row has to do to be at one coverage item of a border.
 *
 * <p>Two kinds and not four. {@code ON} and {@code OFF} name a place and are met by writing it;
 * {@code IN} and {@code OUT} name a side and are met by landing anywhere in it. Which of the four
 * roles a criterion belongs to is the border's to say ({@link PointRole}) and is no part of this: the
 * same shape answers for two roles, and a criterion that carried the role would have every reader
 * deciding what to compare from a word rather than from what it was handed.
 *
 * <p>What a row has to reach beyond that is not here either. A line a fork of a body drew is met by
 * getting the comparison to answer as well as by writing the value, and that is true of all four of
 * its points — it is a fact about the rule that drew the border, so it is asked of the border and
 * never of the item.
 */
public sealed interface Criterion {

    /** A row whose place at this position is exactly this one. */
    record AtThePlace(souther.compiler.numeric.Place place) implements Criterion {}

    /**
     * A row that writes one place at both terms of a line between two positions.
     *
     * <p>No place of its own. Where the line is is a relation the row satisfies, and the value a
     * search happens to find that satisfies it is a witness — written here, one row on the line would
     * name every other row on it a different item.
     */
    record WhereTheTermsMeet() implements Criterion {}

    /** A row anywhere in one side of the border, away from the line. */
    record InTheRegion(Region region) implements Criterion {}

    /**
     * What this asks of a row, as a report writes it: the relation and what it is against.
     *
     * <p>Written whole rather than as a value beside an operator a reader supplies. Two of the four
     * items ask for a place and two ask for a side, and a report that printed a value for all four
     * would name a witness of a side as though it were the side — {@code = 99} where what is owed is
     * any row below the line.
     */
    default String asked(BoundaryTarget cut) {
        return operator() + " " + against(cut);
    }

    /** How this relates a row's value to what it is against. */
    default String operator() {
        return switch (this) {
            case AtThePlace _, WhereTheTermsMeet _ -> "=";
            case InTheRegion side -> switch (side.region()) {
                case Region.Beyond beyond -> beyond.towards() == Region.Towards.ABOVE ? ">" : "<";
                case Region.AdmittedOtherThan _ -> "/=";
                case Region.TermsApart apart ->
                        apart.onIsTowards() == Region.Towards.ABOVE ? ">" : "<";
            };
        };
    }

    /**
     * What it is against, as a report writes it: a value on the line's own carrier, or the other
     * position where the line is between two.
     *
     * <p>Apart from {@link #operator()} because the two are read apart. A diagnostic about a point on
     * the line puts the value in a sentence the catalog writes in every language, and the relation is
     * in the sentence rather than in the value.
     */
    default String against(BoundaryTarget cut) {
        return switch (this) {
            case AtThePlace at -> cut.carrier().written(at.place());
            case WhereTheTermsMeet _ -> cut.right();
            case InTheRegion side -> switch (side.region()) {
                case Region.Beyond beyond -> cut.carrier().written(beyond.from());
                case Region.AdmittedOtherThan other -> cut.carrier().written(other.excluded());
                case Region.TermsApart _ -> cut.right();
            };
        };
    }
}
