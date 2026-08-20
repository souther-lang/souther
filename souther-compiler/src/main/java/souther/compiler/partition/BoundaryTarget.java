package souther.compiler.partition;

/**
 * What a line is drawn at: a quantity, and where on it the rule cuts.
 *
 * <p><b>A product and no longer a sum.</b> What differs between a line at a position's own value, a
 * line where two positions stand apart and a line over an arithmetic form is <em>what is being
 * cut</em> — and that is {@link BorderQuantity}'s one answer rather than a shape every reader of a
 * line has to tell apart. Written as a sum here, a shape added was a shape a report, a row check, a
 * generator, a probe, an assessment and a criterion vocabulary each grew an arm for; the second one
 * cost nine such arms, and the third would have cost nine more.
 *
 * <p>The sentence a line is named by is {@code left = right} whatever it is on, so both are asked
 * here rather than assembled by each reader out of whichever fields it knows about.
 */
public record BoundaryTarget(BorderQuantity of, QuantityCut cut) {

    public BoundaryTarget {
        if (of == null || cut == null) {
            throw new IllegalArgumentException("a line is a quantity cut somewhere");
        }
    }

    /** A line on {@code of} at the level {@code at}. */
    public static BoundaryTarget at(BorderQuantity of, Level at) {
        return new BoundaryTarget(of, new QuantityCut(at));
    }

    /**
     * Which shape this line has, for a reader outside this compiler that has to tell them apart.
     *
     * <p>A published word ({@code partition.boundaries[].kind}) and not a question anything here
     * asks. A report writes a line as {@code left = right} whichever it is, and what stands on the
     * right is a value in one case and a position in another — a consumer reading the right as a
     * value would read a position's name as one, so the shape is said rather than inferred.
     */
    public Shape shape() {
        return of.shape();
    }

    /** The order this line's levels are on. */
    public LevelSpace levels() {
        return of.levels();
    }

    /** Where the rule cut. */
    public Level at() {
        return cut.at();
    }

    /** The left of the line as a report names it, which is qualified by the behavior it is an input
     *  of. Apart from {@link #left()}, which is the bare term a generated row is labelled with. */
    public String named() {
        return of.named();
    }

    /** The left of the {@code left = right} a report names this by. */
    public String left() {
        return of.left();
    }

    /** The right of it, which is where the rule cut, written the way the quantity writes its own
     *  levels. */
    public String right() {
        return of.writtenAt(at());
    }

    /** Which shape a line has, for a reader that has to tell them apart without holding either. */
    public enum Shape {
        /** A count of one position. */
        AT_VALUE,
        /** Two positions holding the same place. */
        BETWEEN_POSITIONS,
        /** An arithmetic form over several positions, at a value of the form. */
        OVER_A_FORM
    }
}
