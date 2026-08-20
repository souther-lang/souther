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
     * A row whose quantity is strictly past {@code from}, the way {@code towards} says.
     *
     * <p>What both sides of a border are. The {@code IN} side starts at the {@code ON} point and runs
     * inwards; the {@code OUT} side starts at the {@code OFF} point and runs outwards. Where the
     * point it would start at is one the order names no value for, it starts at the line itself — the
     * values one step away are not there to be excluded, and everything past the line on that side is
     * as far from the border as anything gets.
     */
    record Beyond(Level from, Towards towards) implements Criterion {

        @Override
        public boolean holds(LevelSpace space, Level value) {
            int order = space.compare(value, from);
            return towards == Towards.ABOVE ? order > 0 : order < 0;
        }

        @Override
        public String operator() {
            return towards == Towards.ABOVE ? ">" : "<";
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

    /** The level this is written against, which is the one every shape has. */
    default Level against() {
        return switch (this) {
            case AtTheLevel at -> at.at();
            case Beyond beyond -> beyond.from();
            case AnythingBut other -> other.excluded();
        };
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
        return operator() + " " + of.writtenAt(against());
    }
}
