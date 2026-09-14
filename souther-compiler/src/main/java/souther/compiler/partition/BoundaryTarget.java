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
 *
 * <p><b>This value is what tells one place a line was read from another.</b> Two of these are equal
 * when they are the same quantity cut at the same place, and nothing about how either was found or
 * printed is in here — which is what lets a reader hold the whole value as an identity instead of
 * keying on a word it can spell. Anything added to it that is not part of what is cut or where —
 * where the reading came from, what a diagnostic wants to say — would start telling two readings of
 * one place apart.
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

    /** Which behavior's input the line is on, which is the quantity's answer. */
    public String behavior() {
        return of.behavior();
    }

    /** The left of the line as a report names it, which is qualified by the behavior it is an input
     *  of. Apart from {@link #left()}, which is the bare term a generated row is labelled with. */
    public String named() {
        return of.named();
    }

    /**
     * The left of the {@code left = right} a report names this by.
     *
     * <p>A word for a reader, and not what tells two of these apart. A quantity runs over as many
     * positions as it runs over and this names one of them, so two lines from one position to two
     * different ones are both written {@code today} here — a map keyed on it holds one of the two.
     * What tells them apart is the whole value; a reader wanting the sentence takes {@link #label}.
     */
    public String left() {
        return of.left();
    }

    /** The right of it, which is where the rule cut, written the way the quantity writes its own
     *  levels. The same caution as {@link #left()}: a word, and not half of a key. */
    public String right() {
        return of.writtenAt(at());
    }

    /** The whole sentence a report names this line by. The one spelling of it, so that a reader
     *  meeting it in two places meets one wording. */
    public String label() {
        return left() + " = " + right();
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
