package souther.compiler.partition;

/**
 * What a row has to do to be at one coverage item of a border.
 *
 * <p>Two questions and four shapes. {@code ON} and {@code OFF} name a place and are met by writing it;
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
     * A row whose {@code on} term stands exactly {@code steps} from its {@code against} term —
     * below where that is negative, above where it is positive, and on the line itself at zero.
     *
     * <p>A line between two positions is a border on the difference the two fall apart by, and this
     * is that border's {@link AtThePlace}. Which is the whole of why the four points of such a line
     * are ordinary: the point one step inside {@code a < b} is the pair where {@code a} is {@code b}
     * less one, and reading it as a place at either term is what made it look like a point nothing
     * could name.
     *
     * <p>No place of its own, at any step. Where the line is is a relation a row satisfies, and the
     * pair a search happens to find that satisfies it is a witness — written here, one row on the
     * line would name every other row on it a different item.
     */
    record WhereTheTermsAreApartBy(int steps) implements Criterion {}

    /**
     * A row whose {@code on} term stands further from its {@code against} term than {@code steps},
     * the way {@code towards} says.
     *
     * <p>The same border's {@link Region.Beyond}: a side of the line, starting past the point
     * against it on that side. Where the carrier names no value one step from the line the side
     * starts at the line itself, which is what a side of a border at a place does for the same
     * reason.
     */
    record WhereTheTermsAreFurtherApartThan(int steps, Region.Towards towards)
            implements Criterion {}

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
            case AtThePlace _ -> "=";
            case WhereTheTermsAreApartBy _ -> "=";
            case WhereTheTermsAreFurtherApartThan apart ->
                    apart.towards() == Region.Towards.ABOVE ? ">" : "<";
            case InTheRegion side -> switch (side.region()) {
                case Region.Beyond beyond -> beyond.towards() == Region.Towards.ABOVE ? ">" : "<";
                case Region.AdmittedOtherThan _ -> "/=";
            };
        };
    }

    /**
     * The other term, stepped, as a report writes it.
     *
     * <p>The step is on the difference and not on either term, so it is written beside the term
     * rather than folded into a value: a reader is told that the point is one step from where the
     * two meet, which is what it is.
     */
    private static String stepped(String term, int steps) {
        return steps == 0 ? term : steps < 0 ? term + " - " + -steps : term + " + " + steps;
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
            case WhereTheTermsAreApartBy apart -> stepped(cut.right(), apart.steps());
            case WhereTheTermsAreFurtherApartThan apart -> stepped(cut.right(), apart.steps());
            case InTheRegion side -> switch (side.region()) {
                case Region.Beyond beyond -> cut.carrier().written(beyond.from());
                case Region.AdmittedOtherThan other -> cut.carrier().written(other.excluded());
            };
        };
    }
}
