package souther.compiler.partition;

/**
 * One run of values a quantity's rules leave between two of the places they part it.
 *
 * <p>What a class of a position is, and what the {@code IN} point of a border beside it asks for.
 * The two used to be derived apart, and only the first of them knew about the lines further along —
 * so a row well past the next line answered for a point that was supposed to be inside this run.
 *
 * @param under the seam this run starts above, or null where nothing parts it there
 * @param over  the seam it stops below, or null on the same reading
 * @param from  what the rules leave the quantity at the low end, which is where a run with no seam
 *              under it starts. Null where they leave it everything that way
 * @param to    the same at the high end
 */
public record Band(Seam under, Seam over, Level from, Level to) {

    /**
     * How this run reads: the first value in it and the last.
     *
     * <p>Taken from the seams either side rather than held, so that a run and the places that part
     * it can never say different things about where it starts. An end the order itself supplies is
     * written as nothing, because there is no value there to name.
     */
    public String key() {
        return where(first()) + "|" + where(last());
    }

    /** The first value in this run, or null where the order names none there. */
    public Level first() {
        return under == null ? from : under.above();
    }

    /** The last, on the same reading. */
    public Level last() {
        return over == null ? to : over.below();
    }

    /**
     * This run as a report writes it, in the same words the class of a position that is this run is
     * named by.
     *
     * <p>Written from the lines either side rather than from the values at its ends, which is what
     * lets one spelling answer for every carrier: a run above a line at ten is {@code 10 < x} on the
     * whole numbers and on the decimals alike, while the value it starts at exists only on the
     * first. One spelling, so that the class a report counts and the point a border owes inside it
     * are visibly the same run.
     */
    public String written(BorderQuantity of) {
        return written(of, null);
    }

    /**
     * The same, without one value of it.
     *
     * <p>Which is what a point away from a border asks for: the run, less the value against the
     * line. Said as the run alone, a reader is told to write a row anywhere up to a hundred when a
     * hundred is the one value that will not do.
     */
    public String written(BorderQuantity of, Level except) {
        String low = except != null && same(except, first())
                ? of.writtenAt(except) + " < "
                : under != null ? of.writtenAt(under.at().written()) + opens(under)
                        : from == null ? "" : of.writtenAt(from) + " <= ";
        String high = except != null && same(except, last())
                ? " < " + of.writtenAt(except)
                : over != null ? closes(over) + of.writtenAt(over.at().written())
                        : to == null ? "" : " <= " + of.writtenAt(to);
        return low.isEmpty() && high.isEmpty() ? "any" : (low + of.left() + high).trim();
    }

    /** Whether this run has any value in it other than {@code except}, where that can be settled.
     *  A run one value wide whose one value is against the line has nothing away from the line. */
    public boolean holdsAnythingBut(Level except) {
        return except == null || first() == null || last() == null
                || !first().key().equals(last().key()) || !same(except, first());
    }

    private static boolean same(Level one, Level other) {
        return one != null && other != null && one.key().equals(other.key());
    }

    /** Whether the line below this run keeps its own value, which decides whether the run starts
     *  past that value or at it. */
    private static String opens(Seam under) {
        return keepsItsOwnValueBelow(under) ? " < " : " <= ";
    }

    private static String closes(Seam over) {
        return keepsItsOwnValueBelow(over) ? " <= " : " < ";
    }

    private static boolean keepsItsOwnValueBelow(Seam seam) {
        return seam.below() != null && seam.below().key().equals(seam.at().written().key());
    }

    /**
     * Whether a value of the quantity lies in this run.
     *
     * <p>Both ends included, because a run is named by the values at its ends and not by the lines
     * beside it: the first value above a seam is in the run above and the last value below is in the
     * run below. An end the order supplies rather than a rule leaves that side open.
     *
     * <p>Where a seam names no value on the side facing this run — a carrier whose values fill has
     * no first value above a line it keeps — the run is open at the line itself, which is where the
     * seam's own position says the values part.
     */
    public boolean holds(LevelSpace space, Level value) {
        return past(space, value, under, Towards.ABOVE) && past(space, value, over, Towards.BELOW)
                && within(space, value, from, Towards.ABOVE) && within(space, value, to,
                        Towards.BELOW);
    }

    /** Whether {@code value} is on this run's side of one of the seams that part it. */
    private static boolean past(LevelSpace space, Level value, Seam seam, Towards side) {
        if (seam == null) {
            return true;
        }
        Level edge = side == Towards.ABOVE ? seam.above() : seam.below();
        if (edge != null) {
            return within(space, value, edge, side);
        }
        // No value on this side of the line, so the run is open at the line: what parts the values
        // is the position itself, and every value of the quantity that way is in this run. Asked of
        // the position, because the rule may have written a multiple of the quantity and the value
        // is one of the quantity's own — compared as they stand, a line at a third kept every
        // decimal up to one below it.
        int order = seam.at().compare(value);
        return side == Towards.ABOVE ? order > 0 : order < 0;
    }

    /** Whether {@code value} is at {@code edge} or on the {@code side} of it this run lies. */
    private static boolean within(LevelSpace space, Level value, Level edge, Towards side) {
        if (edge == null) {
            return true;
        }
        int order = space.compare(value, edge);
        return side == Towards.ABOVE ? order >= 0 : order <= 0;
    }

    private static String where(Level at) {
        return at == null ? "" : at.key();
    }
}
