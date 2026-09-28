package souther.compiler.query;

/**
 * Which of the two readings of a line a caller asked for.
 *
 * <p>Named alternatives and not a dial. The two are different ways of finding out whether a row can
 * be written at a point, and what separates them is where the answer comes from: one derives it from
 * the rules the model carries, the other builds a value and puts it through this module's decoders.
 * Ordered as more and less, a third reading added later would have to fit on the same line, and the
 * three are not obliged to.
 *
 * <p>Which lines there are is not this. A point is read wherever the model carries the rule, and the
 * points are the same under both — what moves is what is known about each of them.
 *
 * <p>Asked by whoever puts the question. A measurement derives it from what the build asked to be
 * told; a caller asking for rows composes, because the row is the answer and a reading that built
 * none has nothing to hand over.
 */
public enum HowALineIsRead {

    /** What the model's own rules say, and nothing built. A point inside what every rule reaching it
     *  leaves is writable because the rules say so, and a point only a value could settle stays
     *  unknown — reported, and counted against nobody. */
    THE_RULES_ALONE,

    /** That, and a value composed at every point worth one and run through this module's decoders.
     *  What it costs is a decoder run per point, and what it buys is an answer at the points the
     *  rules do not reach, along with the row an author is offered there. */
    VALUES_COMPOSED
}
