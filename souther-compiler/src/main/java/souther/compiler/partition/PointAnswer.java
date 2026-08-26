package souther.compiler.partition;

import java.util.List;

/**
 * What a border says about one of its four points: what a row there has to do, and what such a row
 * is owed for.
 *
 * <p>The two together, from the one reading that settled both. What a row has to do is read off the
 * order the quantity sits on; what it is owed for is the line, and — away from the line — whatever
 * stops the region on the far side. Both are decided in the same branch of the same procedure, and
 * handing over only the first left every reader downstream to work the second out again from the
 * criterion, the values, and the reading it turned up in. That is how the reading came to stand in
 * for the identity.
 *
 * <p>Sealed over the two kinds of point a border has, so a point against the line cannot come back
 * carrying a region and a region cannot come back without one. Which of the two a role is, is
 * {@link PointRole#againstTheLine}'s answer and the border holds itself to it.
 */
public sealed interface PointAnswer {

    /** No row is asked for here, and this is what settles it. */
    record NotOwed(NotOwedReason reason) implements PointAnswer {

        public NotOwed {
            if (reason == null) {
                throw new IllegalArgumentException("a point nobody is owed a row at says why");
            }
        }
    }

    /** A row at the line itself, which is a value of the quantity and the same value wherever the
     *  line is read. */
    record AtLine(Criterion criterion) implements PointAnswer {

        public AtLine {
            if (criterion == null) {
                throw new IllegalArgumentException("a row against the line has something to do");
            }
        }
    }

    /**
     * A row somewhere in the region on one side of the line.
     *
     * @param criterion what such a row has to do
     * @param bases     what it is owed for, beside the line: one per thing that settled where the
     *                  region stops, each of them enough on its own. Never empty
     */
    record InRegion(Criterion criterion, List<RegionBasis> bases) implements PointAnswer {

        public InRegion {
            if (criterion == null) {
                throw new IllegalArgumentException("a row in the region has something to do");
            }
            bases = List.copyOf(bases);
            if (bases.isEmpty()) {
                throw new IllegalArgumentException(
                        "a region a row is owed in is owed for something: " + criterion);
            }
            // The whole of the quantity but one value is not a run and stops nowhere, so nothing
            // stands beside it. Held together with a run's ends, a reader would be told the region
            // both is and is not bounded.
            if (bases.contains(RegionBasis.THE_REST) && bases.size() != 1) {
                throw new IllegalArgumentException(
                        "what a rule leaves outside the value it names is not beside anything: "
                                + bases);
            }
        }
    }

    /** What a row here has to do, or null where none is asked for. */
    default Criterion criterion() {
        return switch (this) {
            case NotOwed _ -> null;
            case AtLine at -> at.criterion();
            case InRegion in -> in.criterion();
        };
    }

    /**
     * What is asked of a row here, without what it would be owed for.
     *
     * <p>For a reader measuring rows against points rather than accounting for them. Everything that
     * says what a row has to do goes through this, so the two cannot come apart.
     */
    default Demand demand() {
        Criterion asked = criterion();
        return asked == null
                ? new Demand.NotOwed(((NotOwed) this).reason()) : new Demand.Owed(asked);
    }

    /** What a row here is owed for beside the line, which is nothing for a point against it. */
    default List<RegionBasis> bases() {
        return this instanceof InRegion in ? in.bases() : List.of();
    }
}
