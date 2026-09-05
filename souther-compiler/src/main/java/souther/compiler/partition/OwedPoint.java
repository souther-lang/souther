package souther.compiler.partition;

/**
 * A point a row is owed at, as one reading of one border says it: what is owed, and whose account
 * it falls in.
 *
 * <p>Both from the one branch that worked the region out, because both are known there and neither
 * can be worked out from the other afterwards. Which point this is is settled by the model and is
 * the same wherever the line is read; whose account it falls in is a fact about this reading's
 * surroundings and is no part of which point it is.
 *
 * <p>Read off the point instead — the lines that happen to be inside its identity — a run stopping
 * where a declaration took the position in came back owed to the line below it and to nobody else,
 * and the declaration that put the end there was told nothing about a row it could be asked for.
 *
 * <p>Two things, and they answer different questions: the point is what a row here is owed for,
 * which two readings of it share, and the attribution is whose it is to write that row, as this
 * reading settled it.
 */
public final class OwedPoint {

    private final BorderObligationPoint point;
    private final PointAttribution attribution;

    /**
     * Made where a border says what it owes, and nowhere else.
     *
     * <p>Package-private for that reason. Whose it is to write a row here is read off everything
     * that settled the point ({@link PointAttribution#of}), and a value anybody could assemble is a
     * way to hand an account an answer that classifier never gave — the arm chosen by whoever was
     * writing rather than by what the model says.
     */
    OwedPoint(BorderObligationPoint point, PointAttribution attribution) {
        if (point == null || attribution == null) {
            throw new IllegalArgumentException(
                    "a point owed a row is owed for something, by somebody: " + point);
        }
        this.point = point;
        this.attribution = attribution;
    }

    /** What a row here is owed for, which two readings of it share. */
    public BorderObligationPoint point() {
        return point;
    }

    /** Whose it is to write a row here, as this reading settled it. */
    public PointAttribution attribution() {
        return attribution;
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof OwedPoint that
                && point.equals(that.point) && attribution.equals(that.attribution);
    }

    @Override
    public int hashCode() {
        return java.util.Objects.hash(point, attribution);
    }

    @Override
    public String toString() {
        return point + " owed to " + attribution;
    }
}
