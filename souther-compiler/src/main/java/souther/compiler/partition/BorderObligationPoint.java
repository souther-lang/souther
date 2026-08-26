package souther.compiler.partition;

/**
 * One point of one authored line: what a row is owed for, once, however many positions carry it.
 *
 * <p>The unit a generation answers at. A line is owed by whoever wrote it ({@link
 * BorderObligationId}) and asks something different at each of the points against it — a row at the
 * line and a row beside it are two values and two pieces of work — so neither half identifies the
 * work on its own.
 *
 * <p>The two regions either side are not addressed here. Where a region stops is settled by every
 * other rule reaching a position, so a row well inside one is a row at that position rather than at
 * the line, and it is owed per reading ({@link PointRole#againstTheLine}).
 */
public record BorderObligationPoint(BorderObligationId line, PointRole role) {

    public BorderObligationPoint {
        if (line == null) {
            throw new IllegalArgumentException("a point is some authored line's");
        }
        if (role == null || !role.againstTheLine()) {
            throw new IllegalArgumentException(
                    "a point of a line is one of the two against it, and " + role
                            + " is a region of a position");
        }
    }
}
