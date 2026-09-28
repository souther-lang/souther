package souther.compiler.check;

/**
 * What an expansion puts where a value's name was written.
 *
 * <p>One question with three answers, and a representation picks the one its readers can read. A
 * value denotes as if its body stood at each reference (ADR-0072); this is how that denotation is
 * realised, and the three differ in what the reader below is able to do with what it is handed.
 *
 * <p>Apart from {@link InliningPolicy}, which is a different question about a different thing. That
 * one says which <em>calls</em> a representation keeps standing, and it is about what an analysis
 * has rules for. This says what a <em>value reference</em> becomes, and it is about whether the
 * reader can emit what it is given. A representation answers both, and neither answer follows from
 * the other.
 */
public enum ValueAtAReference {

    /**
     * A fresh copy of the body, spliced where the name was written.
     *
     * <p>What a reader that cannot read a binding needs. A value named twice is copied twice, and
     * one whose body names another is copied with that one inside it, so what a body holds is what
     * its references multiply out to rather than what the source wrote.
     */
    COPIED,

    /**
     * The reference itself, standing under the signature the value's own check settled.
     *
     * <p>For a reader that has the value's answer already and needs nothing from its body
     * ({@link Preserved#valuesAlreadySettled}). Nothing is emitted from a tree in this form: the
     * reference names a definition the backend has no method for.
     */
    SETTLED_REFERENCE,

    /**
     * A local the expansion bound once in the region that demands it, read where the name was
     * written.
     *
     * <p>The body stands once per evaluation region rather than once per reference, which is what
     * keeps what a body holds proportional to what the source wrote. A reader emits it as it emits
     * any other binding, so this is the form a tree that runs is built in.
     *
     * <p>Bounded by the region and not by the body. Bound outside one, a value would be evaluated
     * on a path no reference of it is reached on — the value is pure and total, so the answer is
     * the same, but the work is not, and the work is what this is for.
     */
    SHARED_PER_REGION
}
