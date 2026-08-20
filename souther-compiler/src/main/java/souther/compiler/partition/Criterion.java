package souther.compiler.partition;

/**
 * What a row has to do to be at one coverage item of a border.
 *
 * <p>Said of the border's {@link BorderQuantity} and of nothing else. Three shapes for every border
 * there is: a row is at one level of the quantity, or anywhere beyond one level, or at any level but
 * one. {@code ON} and {@code OFF} are the first; {@code IN} and {@code OUT} are the second, except
 * where the rule leaves a side that is not a run of the order and then they are the third.
 *
 * <p><b>Not one shape per kind of border.</b> A line at a place of one position and a line where two
 * positions stand apart used to ask for two vocabularies here, and every reader of an item had to
 * know which of the two it was holding — a criterion about a place handed to the reader of a pair was
 * an {@code IllegalStateException} rather than a build failure. What tells them apart is the
 * quantity, and the quantity is what the item is about; what it asks of a row is the same three
 * questions whichever quantity it is on.
 *
 * <p>Which of the four roles a criterion belongs to is the border's to say ({@link PointRole}) and is
 * no part of this: the same shape answers for two roles, and a criterion that carried the role would
 * have every reader deciding what to compare from a word rather than from what it was handed.
 *
 * <p>What a row has to reach beyond that is not here either. A line a fork of a body drew is met by
 * getting the comparison to answer as well as by standing at the level, and that is true of all four
 * of its points — it is a fact about the rule that drew the border, so it is asked of the border and
 * never of the item.
 */
public sealed interface Criterion {

    /** A row whose quantity is exactly this level. */
    record AtTheLevel(Level at) implements Criterion {

        @Override
        public boolean holds(LevelSpace space, Level value) {
            return space.compare(value, at) == 0;
        }

        @Override
        public String operator() {
            return "=";
        }
    }

    /**
     * A row whose quantity lies in one run of the values, other than at one level of it.
     *
     * <p>What both sides of a border are. A border parts two runs, and the {@code IN} point is a row
     * in the one it bounds while the {@code OUT} point is a row in the one it keeps out — in each
     * case away from the line, which is what {@code except} takes out.
     *
     * <p><b>A run and not a side.</b> Read as everything past the line, the point runs to the end of
     * the order, and a row past the next line along answers for it while the run this border bounds
     * has nothing in it. The two are the same only where the quantity has one line through it
     * (issue #880).
     *
     * @param except the value against the line, which is the border's own {@code ON} or {@code OFF}
     *               point and is not this one. Null where the order names no value there, and then
     *               the whole run is what is asked for
     */
    record Within(Band band, Level except) implements Criterion {

        @Override
        public boolean holds(LevelSpace space, Level value) {
            return band.holds(space, value)
                    && (except == null || space.compare(value, except) != 0);
        }

        @Override
        public String operator() {
            return "in";
        }
    }

    /**
     * A row at any level of the quantity other than one.
     *
     * <p>What a border that has no far side leaves. An invariant refuses everything outside its
     * bound, so the side it bounds is the whole of what the quantity takes; a rule that singles a
     * value out puts every other value in one class, and that class is what lies away from the point.
     * Neither of them is a run of the order from somewhere, which is why it is a shape of its own
     * rather than a {@link Beyond} with an end nobody wrote.
     */
    record AnythingBut(Level excluded) implements Criterion {

        @Override
        public boolean holds(LevelSpace space, Level value) {
            return space.compare(value, excluded) != 0;
        }

        @Override
        public String operator() {
            return "/=";
        }
    }

    /**
     * Whether a row whose quantity came to {@code value} is at this item.
     *
     * <p>On the interface because it is what a criterion is. A value stands for an item only where
     * the item says it does, and every shape answers that — asked of one shape and not another, a
     * witness composed for a side stood for it on the strength of the arithmetic that composed it
     * rather than on the item's own answer.
     */
    boolean holds(LevelSpace space, Level value);

    /** How this relates a row's quantity to what it is against. */
    String operator();

    /**
     * The level this is written against, or null where what it is written against is a run rather
     * than a level.
     *
     * <p>Two of the three shapes name a level and one names a region, so a reader that wanted one
     * level from every shape was reading a witness of a run as though it were the run. What every
     * shape does answer is {@link #asked}.
     */
    default Level against() {
        return switch (this) {
            case AtTheLevel at -> at.at();
            case Within _ -> null;
            case AnythingBut other -> other.excluded();
        };
    }

    /**
     * One level this is written around, which every shape has.
     *
     * <p>Apart from {@link #against}, which is what a report writes: a run is not written against a
     * level and is still arranged around one — the value against the line it lies beside. What reads
     * this is the search, which starts from a level and works outward whichever shape it is holding.
     */
    default Level anchor() {
        if (!(this instanceof Within in)) {
            return against();
        }
        if (in.except() != null) {
            return in.except();
        }
        if (in.band().first() != null) {
            return in.band().first();
        }
        if (in.band().last() != null) {
            return in.band().last();
        }
        // A run with no value at either end is arranged around the place its line falls at, which
        // is where the values part and is the only thing left that says where the run starts.
        Seam edge = in.band().under() != null ? in.band().under() : in.band().over();
        return edge == null ? null : edge.at().written();
    }

    /**
     * What this asks of a row, as a report writes it: the relation and what it is against.
     *
     * <p>Written whole rather than as a value beside an operator a reader supplies. Two of the four
     * items ask for a level and two ask for a side, and a report that printed a value for all four
     * would name a witness of a side as though it were the side — {@code = 99} where what is owed is
     * any row below the line.
     *
     * <p>What the level is written as is the quantity's, because only the quantity knows what its
     * numbers are of: a count of days is a date, and how far two positions stand apart is written
     * beside the position it is apart from rather than as the number it is.
     */
    default String asked(BorderQuantity of) {
        return operator() + " " + written(of);
    }

    /**
     * What this is written against, as a report writes it: a level for the shapes that name one, and
     * the run itself for the shape that names a run.
     *
     * <p>The run written whole. A run has two ends and a report that printed one of them would name
     * a value inside it as though it were the run — which is the reading this shape exists to stop.
     */
    default String written(BorderQuantity of) {
        if (!(this instanceof Within in)) {
            return of.writtenAt(against());
        }
        return in.band().written(of, in.except());
    }
}
