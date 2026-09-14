package souther.compiler.partition;

import java.util.List;

/**
 * What a border has in one of the four roles: the points that play it, or why none does.
 *
 * <p>The classification read the other way round. A border's points are places
 * ({@link DomainPoint}) and what each of them is follows from the rule, so the four words of the
 * technique are the classes of that map rather than the map's own keys. Asked only of the points, a
 * word with nothing under it is a word nobody says anything about — which is the silence a total
 * answer over the four roles exists to stop, one turn of the crank up from
 * {@link Demand.NotOwed}.
 *
 * <p><b>And not the same answer as a point owing no row.</b> A point the rules refuse is a place the
 * technique asks about and the model has settled; a role with no point is a word the technique has
 * for something this line does not have. A reader acts on them differently — one is an item counted
 * out, the other is not an item — so they are two answers and never one.
 */
public sealed interface RoleAnswer {

    /** The points of this border playing the role, in the order the border holds them. Never
     *  empty. */
    record Played(List<DomainPoint> at) implements RoleAnswer {

        public Played {
            at = List.copyOf(at);
            if (at.isEmpty()) {
                throw new IllegalArgumentException(
                        "a role nothing plays is answered by why nothing does");
            }
        }
    }

    /** No point of this border is that one, and this is what settles it. */
    record NoPoint(Reason why) implements RoleAnswer {

        public NoPoint {
            if (why == null) {
                throw new IllegalArgumentException("a role this line has no point in says why");
            }
        }
    }

    /**
     * Why a line has no point in one of the four roles.
     *
     * <p>One, because there is one way a role goes unplayed. Written as an enumeration all the same,
     * so that a second way stops the compile where the roles are read rather than arriving as the
     * first one's sentence.
     */
    enum Reason {

        /**
         * The class the line's own value is in holds that value and nothing else, so there is no row
         * in it away from the line.
         *
         * <p>What a rule that names a value leaves. {@code x == 10} puts ten in a class of its own,
         * so it has no {@code IN} point — there is nowhere inside that partition to be away from the
         * border — and {@code x /= 10} has no {@code OUT} point for the same reason one class over.
         */
        THE_CLASS_AT_THE_LINE_HOLDS_ONE_VALUE
    }
}
