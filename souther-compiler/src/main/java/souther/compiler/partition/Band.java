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

    private static String where(Level at) {
        return at == null ? "" : at.key();
    }
}
