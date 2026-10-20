package souther.compiler.inputs;

/**
 * Which question a walk over the input is answering, which decides which of the edges between two
 * bindings' elements it is entitled to cross.
 *
 * <p>Two questions and not one flag. Where a value <em>is</em> and where a value <em>came from</em>
 * are answered by the same steps until a binding holds what an operation made of another's elements:
 * what is made from a position came from it and is not it, so a walk after the position an
 * expression names stops there and a walk after provenance goes on.
 *
 * <p><b>A closed set, and that is what it is for.</b> The edges are not handed out, so the only way
 * to read one is to name one of these; a caller cannot take an edge and decide later what it
 * licenses, and cannot invent a third licence beside these two. What each edge comes to for each
 * question is written in one place ({@link souther.compiler.check.ElementProvenance#stepFrom}),
 * and adding either a question or an edge is a compile error there until somebody says what the pair
 * means.
 */
public enum ElementQuestion {

    /** Which position an expression names, so that a rule about it is a rule about the values a row
     *  writes there. */
    NAMED_POSITION,

    /** Which position a value came from, which is what says a rule was written at all where the
     *  rule is about something made from those values. */
    VALUE_ORIGIN,

    /** Which position holds these very values, every occurrence of it and each as often as the
     *  container holds it, so that a total of them is a total of everything standing there. */
    EVERY_OCCURRENCE,

    /**
     * Which position holds these very values, every occurrence of it once each, in the order the
     * row writes them there — so that where a value stands among them is where it stands in the
     * row.
     *
     * <p>{@link #EVERY_OCCURRENCE} and the order beside it. That one crosses what puts the elements
     * in another order, which a total of them does not see; a number that turns on where each
     * element stands does, so this crosses no operation, only the names and choices a list is
     * written through.
     */
    IN_THE_ORDER_WRITTEN,

    /**
     * Which position holds these very values, every occurrence of it once each, handed from the
     * last the row writes there to the first — so that where a value stands among them is how far
     * it is from the end of the row.
     *
     * <p>{@link #IN_THE_ORDER_WRITTEN} through one operation that answers its list the other way
     * round, and no other: below it the elements are asked in the order written.
     */
    FROM_THE_FAR_END,

    /**
     * Which container of the input a list holds one value for each element of, in the one
     * occurrence of the container the list was made from, and where in the element that value
     * stands — so that how often a value occurs in the list is how often it occurs there.
     *
     * <p>Not {@link #EVERY_OCCURRENCE}: a list made from the items of one order holds those items
     * and none of another order's, and how often a value occurs among them is a number of that
     * order.
     */
    ONE_PER_ELEMENT,

    /** Which container of the input a list holds something exactly where it does, whatever the
     *  values it holds are. */
    SAME_EMPTINESS
}
