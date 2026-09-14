package souther.compiler.partition;

/**
 * One thing a row is owed for: a point of a line the author wrote, once, however many positions
 * carry it.
 *
 * <p>The unit everything downstream accounts in — what a finding is about, what a verdict counts,
 * what a generated row answers. A line is owed by whoever wrote it ({@link BorderObligationId}) and
 * asks something different at each of its points, so neither half identifies the work on its own: a
 * row at the line and a row beside it are two values and two pieces of work.
 *
 * <p><b>And beside the line, what stopped the region is part of it too.</b> A point against the line
 * names a value of the quantity, and the line settles that value wherever it is read — one debt,
 * whichever position met it. A point away from it names a region, and where a region stops is
 * settled by the line together with whatever bounds it on the far side; so two readings of one line
 * are owed one row there only where the far side is the same thing, and that is what
 * {@link FarEnd} carries. Keyed on the line alone, a run stopping at a body's own comparison
 * and a run running to the end of the order were one debt and could not both be answered.
 *
 * <p><b>Not where it was read.</b> Which position of which behavior met the line is an occurrence,
 * and it is evidence: it says a row was looked for and what became of it. Held here, one clause of a
 * type is asked for once per position of every behavior carrying it.
 *
 * <p><b>And not who can move what settled it.</b> That is a fact about the surroundings of the
 * reading rather than about which point this is — two readings that answer it differently are still
 * one point — and it is carried beside this ({@link OwedPoint}). Worked out from what is in here
 * instead, a run stopping where a declaration took the position in came back owed to the line below
 * it and to nobody else.
 */
public sealed interface BorderObligationPoint {

    /** Which line of the model a row here is owed for. */
    BorderObligationId line();

    /**
     * Which point of that line, as a place on the quantity's order.
     *
     * <p>The place and not what it is. Two points of one line can be the same one of the four —
     * a rule that names a value owes a row on each side of it and both of those are outside what it
     * names — so the role tells them apart nowhere. What it is is read off the line that has it
     * ({@link Border#roleOf}), which knows the rule as well as the place.
     */
    DomainPoint point();

    /**
     * Which of the four this is, which the rule that drew the line answers together with the place.
     *
     * <p>A projection and never a key. Two points of one line can come back with one of these, so a
     * reader telling points apart by it is telling apart fewer things than there are. It is here
     * rather than only on the border because a debt outlives the reading it was made at: what a
     * report prints and what a build is held to are about the point, and both want the word.
     */
    default PointRole role() {
        return PointRole.of(point(), line().line().facts().holdsAt(point()));
    }

    /**
     * A row at a value of the quantity: the one the rule wrote, or the one beside it on a side.
     *
     * <p>Whether a row standing at length 1 is believed is a question about the type and not about
     * any body carrying it, so one row anywhere settles it.
     */
    record AtLine(BorderObligationId line, DomainPoint point) implements BorderObligationPoint {

        public AtLine {
            if (line == null) {
                throw new IllegalArgumentException("a point is some authored line's");
            }
            if (point == null || !point.againstTheLine()) {
                throw new IllegalArgumentException(
                        "a point at a value of the quantity is one of the places against the line,"
                                + " and " + point + " is a run beside it");
            }
        }
    }

    /**
     * A row in the region on one side of the line, as far as {@code region} stops it.
     *
     * @param region what settled the region beside the line, which is what tells this from the same
     *               point of the same line where something else stopped it
     */
    record InRegion(BorderObligationId line, DomainPoint point, FarEnd region)
            implements BorderObligationPoint {

        public InRegion {
            if (line == null || region == null) {
                throw new IllegalArgumentException(
                        "a region a row is owed in is some line's, and stops somewhere: " + line
                                + " " + region);
            }
            if (point == null || point.againstTheLine()) {
                throw new IllegalArgumentException("a point in a region is one of the runs beside"
                        + " the line, and " + point + " is at a value of it");
            }
        }
    }
}
