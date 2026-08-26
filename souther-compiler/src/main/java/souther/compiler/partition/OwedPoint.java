package souther.compiler.partition;

/**
 * A point a row is owed at, as one reading of one border says it: what is owed, and who can move
 * what settled it.
 *
 * <p>Both from the one branch that worked the region out, because both are known there and neither
 * can be worked out from the other afterwards. Which point this is is settled by the model and is
 * the same wherever the line is read; who can move what settled it is a fact about this reading's
 * surroundings and is no part of which point it is.
 *
 * <p>Read off the point instead — the lines that happen to be inside its identity — a run stopping
 * where a declaration took the position in came back owed to the line below it and to nobody else,
 * and the declaration that put the end there was told nothing about a row it could be asked for.
 *
 * @param point       what a row here is owed for, which two readings of it share
 * @param attribution who settled that, at this reading
 */
public record OwedPoint(BorderObligationPoint point, PointAttribution attribution) {

    public OwedPoint {
        if (point == null || attribution == null) {
            throw new IllegalArgumentException(
                    "a point owed a row is owed for something, by somebody: " + point);
        }
    }

    /** Which of a border's four points this is. */
    public PointRole role() {
        return point.role();
    }
}
