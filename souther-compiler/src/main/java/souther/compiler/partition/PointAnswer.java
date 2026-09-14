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
            if (!(criterion instanceof Criterion.AtTheLevel)) {
                throw new IllegalArgumentException(
                        "a row against the line stands at a level of the quantity, and this asks "
                                + criterion);
            }
        }
    }

    /**
     * A row somewhere in the region on one side of the line.
     *
     * @param criterion what such a row has to do
     * @param claims    what it is owed for and who can move that, one per thing that settled where
     *                  the region stops, each of them enough on its own. Never empty, and one entry
     *                  per basis
     */
    record InRegion(Criterion criterion, List<RegionClaim> claims) implements PointAnswer {

        public InRegion {
            if (criterion == null) {
                throw new IllegalArgumentException("a row in the region has something to do");
            }
            claims = List.copyOf(claims);
            if (claims.isEmpty()) {
                throw new IllegalArgumentException(
                        "a region a row is owed in is owed for something: " + criterion);
            }
            List<FarEnd> bases = claims.stream().map(RegionClaim::basis).toList();
            if (bases.size() != java.util.Set.copyOf(bases).size()) {
                throw new IllegalArgumentException("a region owed twice for one thing, which is"
                        + " once: " + bases);
            }
            // And what is asked of a row is a run of the quantity's values. Every region beside a
            // line is one — the values under it and the values over it, however the rule that drew
            // it divides them — so a region asked for as anything else is a demand and a basis that
            // were not made together.
            if (!(criterion instanceof Criterion.Within)) {
                throw new IllegalArgumentException("a region owed for " + bases
                        + " and asked for as " + criterion);
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

    /** What a row here is owed for beside the line and who can move it, which is nothing for a
     *  point against the line. */
    default List<RegionClaim> claims() {
        return this instanceof InRegion in ? in.claims() : List.of();
    }

    /** The same, as what a row is owed for alone — which is what a point is identified by and what
     *  two readings of one border are compared on. */
    default List<FarEnd> bases() {
        return claims().stream().map(RegionClaim::basis).toList();
    }
}
