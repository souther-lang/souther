package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;

/**
 * What a line is drawn at.
 *
 * <p>A rule draws a line somewhere, and where that is has more than one shape. A rule that compares a
 * position against a constant puts it at one count of one position. A rule that compares one position
 * against another puts it where the two hold the same count, which is a place no single position has a
 * value at — so the two cannot be one record without one of them carrying a field the other has no
 * answer for.
 *
 * <p><b>Sealed, so a shape added is one every reader has to answer for.</b> What a report prints, what
 * a row is checked against and what the generator builds are three readings of a line, and a reader
 * that assumed a count where there is none would print a witness as though it were the line itself.
 *
 * <p>The sentence a line is named by is {@code left = right} whatever its shape, so both are asked
 * here rather than assembled by each reader out of whichever fields it knows about.
 */
public sealed interface BoundaryTarget {

    /**
     * A line at one count of one position.
     *
     * <p>The place is the count and the carrier it is on. Everything that compares a row against this
     * compares counts, and everything that writes or prints it asks the carrier — so a report, a
     * generated row and the rule that drew the line cannot disagree about which value the line is at.
     */
    /**
     * Which shape a line has, for a reader that has to tell them apart without holding either.
     *
     * <p>A report writes a line as {@code left = right} whichever it is, and what stands on the right
     * is a value in one case and a position in the other. A consumer reading the right as a value
     * would read a position's name as one, so the shape is said rather than inferred.
     */
    enum Shape {
        /** A count of one position. */
        AT_VALUE,
        /** Two positions holding the same count. */
        BETWEEN_POSITIONS
    }

    record AtCount(AxisId axis, Carrier carrier, Count at) implements BoundaryTarget {

        @Override
        public Shape shape() {
            return Shape.AT_VALUE;
        }

        @Override
        public String named() {
            return axis.toString();
        }

        @Override
        public String left() {
            return axis.term();
        }

        @Override
        public String right() {
            return carrier.written(at);
        }
    }

    /**
     * A line where two terms hold the same count.
     *
     * <p>Drawn by a {@code guard} comparing one position against another. It divides neither of them —
     * which values of one are on which side depends on the other, and a class is a set of values of one
     * position — so this is a line without a partition, and the two answers are kept apart rather than
     * the second refusing the first.
     *
     * <p>No count. Where the line is is a relation the row satisfies, and the value a search happens to
     * find that satisfies it is the witness rather than the line: written here, one row at the line
     * would name every other row at it as a different boundary.
     *
     * <p>One carrier, because both sides count on it. Two operands may be comparable and count on
     * nothing — a {@code String} is ordered and has no count, and an enumeration's case is comparable
     * on its sum's order without ranging over it — so what makes this line measurable is the carrier
     * and not the type the comparison type-checked under.
     */
    record EqualTerms(String behavior, NumericTerm on, NumericTerm against, Carrier carrier)
            implements BoundaryTarget {

        @Override
        public Shape shape() {
            return Shape.BETWEEN_POSITIONS;
        }

        @Override
        public String named() {
            return new AxisId(behavior, on.toString()).toString();
        }

        @Override
        public String left() {
            return on.toString();
        }

        @Override
        public String right() {
            return against.toString();
        }
    }

    /** Which of the shapes this is. */
    Shape shape();

    /** What the line is on, which is the same carrier for every side of it. */
    Carrier carrier();

    /** The left of the line as a report names it, which is qualified by the behavior it is an input
     * of. Apart from {@link #left()}, which is the bare term a generated row is labelled with. */
    String named();

    /** The left of the {@code left = right} a report names this by. */
    String left();

    /** The right of it. */
    String right();
}
