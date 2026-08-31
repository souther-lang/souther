package souther.compiler.inputs;

/**
 * What a reading of where an expression stands came to.
 *
 * <p>Three answers and not two, because two of them are about the model and one is about this
 * compiler. A position reached is one; an expression that names none — arithmetic over a value, a
 * branch between two, something built — is the model saying there is nothing there, and a reader is
 * told so. What is neither is a shape this reading does not follow: the model may well name a
 * position through it, and nothing here knows which.
 *
 * <p><b>The third is why this is a type.</b> Held as an absent path beside the second, a reading
 * that ran out of what it could follow came back as a model that states nothing — and every sentence
 * written from that absence said of somebody's model what was true of this compiler. There is no
 * spelling of "no path" that carries the difference, so it is carried by which answer this is.
 *
 * <p><b>No way to collapse them but writing it out.</b> A caller for which the last two are one
 * answer says so where it asks, arm by arm, and there is nothing here to say it with — a method
 * that answered "the position, or nothing" would be that decision made once for every caller, and
 * an answer added later would arrive at all of them as nothing without one of them being asked.
 * What the arms cost a reader is that every one of those decisions is visible, which is what they
 * are.
 */
public sealed interface PathResolution {

    /** Where the expression stands. */
    record At(TermPath path) implements PathResolution {}

    /**
     * The expression names no position of the input, which is a fact about the model.
     *
     * <p>What a rule about such a value comes to is a question elsewhere — it may have come from a
     * position, and where it did that is said ({@link InputReads#cameFrom}) — and this is the answer
     * that it does not stand at one.
     */
    record NotAPosition() implements PathResolution {}

    /**
     * A shape this reading does not follow, so whether the expression names a position is not
     * known here.
     *
     * <p>Kept apart from an absence and never turned into one. A reader acting on this is looking
     * at what this compiler does not read yet, and a reader acting on an absence is looking at what
     * their model says.
     */
    record Unread(Reason reason) implements PathResolution {}

    /** Which shape it was, for a reader that says so out loud. */
    enum Reason {

        /**
         * A name bound inside the expression itself.
         *
         * <p>A helper applied to an argument is left as the helper's body under a name bound to it,
         * so an expression handed over may bind names the walk that handed it over never went under.
         * What such an expression comes to is what its body comes to, and reading it takes settling
         * whether the name stands for the position its value names or only for a value made from
         * one — which is a question about the model that this reading does not answer.
         */
        A_NAME_BOUND_INSIDE_THE_EXPRESSION
    }
}
