package souther.compiler.partition;

/**
 * One run of values a quantity's rules leave between two of the places they part it.
 *
 * <p>What a class of a position is, and what the {@code IN} point of a border beside it asks for.
 * The two used to be derived apart, and only the first of them knew about the lines further along —
 * so a row well past the next line answered for a point that was supposed to be inside this run.
 *
 * @param under the seam this run starts above, or null where it runs to the order's own end
 * @param over  the seam it stops below, or null on the same reading
 */
public record Band(Seam under, Seam over) {

    /**
     * How this run reads: the first value in it and the last.
     *
     * <p>Taken from the seams either side rather than held, so that a run and the places that part
     * it can never say different things about where it starts. An end the order itself supplies is
     * written as nothing, because there is no value there to name.
     */
    public String key() {
        return where(under == null ? null : under.above()) + "|"
                + where(over == null ? null : over.below());
    }

    private static String where(Level at) {
        return at == null ? "" : at.key();
    }
}
