package souther.compiler.partition;

import souther.compiler.numeric.Towards;

/**
 * What stops a run of a quantity's values on one side.
 *
 * <p>Three things can, and they are not the same thing. A rule can part the values there, and then
 * the run is named after that line and whoever wrote it. The rules can leave the quantity nothing
 * past a place, and then the run stops where every rule together leaves off — which is not one rule's
 * line and has no one author. Or nothing stops it, and the run goes as far as the order does.
 *
 * <p>Held as three shapes because a reader acts on which of them it is. It used to be a seam that
 * might be null beside an end that might be null, and the three states were the four combinations
 * with one left over: a caller that wanted the line asked whether the seam was there, and a caller
 * that wanted where the run reaches asked both and worked out the tighter. Which of the three a run
 * has is now what it says.
 *
 * <p><b>Where the run reaches is the end's own answer.</b> A line parts the values and the rules
 * leave the quantity an end, and a run is on this side of the line and inside what the rules leave
 * at once — so a run parted by a line the rules stop short of reaches the rules' end and not the
 * line. The two are brought together where the run is built, which is the one place that holds
 * both.
 */
public sealed interface BandEnd {

    /**
     * A rule parts the values here.
     *
     * @param seam    where they part, which is what the run is named after
     * @param reaches how far the run gets on this side, which is the line or what the rules leave,
     *                whichever is the tighter
     */
    record AtParting(Seam seam, Bound reaches) implements BandEnd {

        public AtParting {
            if (seam == null) {
                throw new IllegalArgumentException("a run parted here is parted by something");
            }
        }
    }

    /**
     * The rules leave the quantity nothing past here, and no line parts the values.
     *
     * <p>What every rule about the position leaves together, and the order's own extent among them:
     * a length is never negative and no clause says so. So this is where the run stops and not who
     * stopped it, which is a question about the reading that produced the end rather than about the
     * run.
     */
    record AtDomain(Bound reaches) implements BandEnd {

        public AtDomain {
            if (reaches == null) {
                throw new IllegalArgumentException("an end the rules leave is somewhere");
            }
        }
    }

    /** Nothing stops the run this way: it runs as far as the order does. */
    record AtOrderEnd(Towards towards) implements BandEnd {

        public AtOrderEnd {
            if (towards == null) {
                throw new IllegalArgumentException("an end of the order is one of its two");
            }
        }
    }

    /**
     * How far the run gets on this side, or null where nothing stops it.
     *
     * <p>The one answer about where the run reaches, so that whether a value is in it and where to
     * look for one cannot come apart.
     */
    default Bound reaches() {
        return switch (this) {
            case AtParting parted -> parted.reaches();
            case AtDomain domain -> domain.reaches();
            case AtOrderEnd _ -> null;
        };
    }

    /** The line that parts the values here, or null where nothing parts them and the run stops for
     *  another reason. */
    default Seam parting() {
        return this instanceof AtParting parted ? parted.seam() : null;
    }
}
