package souther.compiler.partition;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Towards;

/**
 * Where the values of a quantity can lie because of what the language holds, whatever any rule
 * says ({@link souther.compiler.inputs.RepresentationBounds}).
 *
 * <p>Asked whether a value can stand somewhere, and never what the position is divided into. A
 * length past the longest string is a length no value has, so a line on it reaches nothing and a
 * point there cannot be written; but that the longest string is where strings stop is no
 * distinction a model made, so it is no end the classes of a position are drawn to and no line of
 * its own. Met into the run the rules leave, it would be both: a relation between two lengths
 * would hold the longest string as a class of its own, which only a string of that length can
 * fill.
 *
 * @param range where the quantity lies, open on a side the language ends nowhere
 */
public record HeldByTheLanguage(NumericDomain.Bounds range) {

    /** A quantity the language ends nowhere. */
    public static final HeldByTheLanguage NOWHERE = new HeldByTheLanguage(NumericDomain.Bounds.OPEN);

    public HeldByTheLanguage {
        if (range == null) {
            throw new IllegalArgumentException("what the language holds of a quantity is a run,"
                    + " open where it holds nothing");
        }
    }

    /** Whether a value of the quantity can stand at {@code level}. A level that is no number is
     *  not one the language ends. */
    boolean admits(Level level) {
        ExactRatio number = level.asANumber();
        return number == null || range.admits(number);
    }

    /** Whether the language leaves nothing in {@code part}: it starts past the last value or stops
     *  before the first. */
    boolean admitsNothingIn(LevelInterval part) {
        return startsPast(part.low()) || stopsBefore(part.high());
    }

    private boolean startsPast(Bound from) {
        ExactRatio most = range.max() == null ? null : numberOf(range.max().at());
        ExactRatio line = from == null ? null : from.at().exactly();
        if (most == null || line == null) {
            return false;
        }
        int order = line.compareTo(most);
        return order > 0 || (order == 0 && !from.inclusive());
    }

    private boolean stopsBefore(Bound to) {
        ExactRatio least = range.min() == null ? null : numberOf(range.min().at());
        ExactRatio line = to == null ? null : to.at().exactly();
        if (least == null || line == null) {
            return false;
        }
        int order = line.compareTo(least);
        return order < 0 || (order == 0 && !to.inclusive());
    }

    /** Whether a value can stand on the {@code side} of {@code level}, at it too where
     *  {@code including}. */
    boolean holdsOnSide(Level level, Towards side, boolean including) {
        ExactRatio number = level.asANumber();
        if (number == null) {
            return true;
        }
        if (side == Towards.ABOVE) {
            ExactRatio most = range.max() == null ? null : numberOf(range.max().at());
            return most == null || (including ? number.compareTo(most) <= 0
                    : number.compareTo(most) < 0);
        }
        ExactRatio least = range.min() == null ? null : numberOf(range.min().at());
        return least == null || (including ? number.compareTo(least) >= 0
                : number.compareTo(least) > 0);
    }

    /** The ends of the run as the first and last value the quantity takes there, for what asks
     *  whether a line leaves nothing on a side. */
    DomainEnds ends(LevelSpace space, Level like) {
        return DomainEnds.of(side -> DomainEnd.heldBy(space, like, range, side));
    }

    private static ExactRatio numberOf(Place at) {
        return at instanceof Count count ? count.exactly() : null;
    }
}
