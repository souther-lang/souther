package souther.compiler.partition;

import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Objects;

/**
 * A point of one reading of a line no row is owed at, and whose fact that is.
 *
 * <p>The counterpart of {@link OwedPoint}, made in the same place from the same answer
 * ({@link Border#leavesOut}). Whose a point is follows from what settled it whether or not a row is
 * owed there: a point only a type's own clauses settled is a fact about the type, said once for
 * the declarations that wrote them, and a point a body's comparison settled is that body's. A
 * reader handed the point without this has to decide it again, and a reader filing it by the line
 * alone files it by another rule than the one a point a row is owed at is filed by.
 */
public final class LeftOutPoint {

    private final NotOwedPoint point;
    private final PointAttribution attribution;

    LeftOutPoint(NotOwedPoint point, PointAttribution attribution) {
        if (point == null || attribution == null) {
            throw new IllegalArgumentException(
                    "a point no row is owed at is some fact, and somebody's: " + point);
        }
        this.point = point;
        this.attribution = attribution;
    }

    public NotOwedPoint point() {
        return point;
    }

    public PointAttribution attribution() {
        return attribution;
    }

    /**
     * Which of the declarations whose fact this is {@code module} wrote, in the order the
     * attribution names them; none where a body's rule settled it, or where none of them is this
     * module's.
     *
     * <p>The question a module's account of what its declarations leave out asks, put here as a
     * debt's is put on the point it is about, so the arms are read in one place.
     */
    public List<TypeSymbol.AtModule> ownersIn(String module) {
        return attribution instanceof PointAttribution.TheDeclarations owned
                ? owned.ownersIn(module) : List.of();
    }

    /** Whether a body's own rule settled this, which makes it that body's to say. */
    public boolean owedToTheReading() {
        return attribution instanceof PointAttribution.TheReading;
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof LeftOutPoint that
                && point.equals(that.point) && attribution.equals(that.attribution);
    }

    @Override
    public int hashCode() {
        return Objects.hash(point, attribution);
    }

    @Override
    public String toString() {
        return point + " left out by " + attribution;
    }
}
