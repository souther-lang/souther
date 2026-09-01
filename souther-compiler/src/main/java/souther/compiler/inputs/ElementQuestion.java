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
    VALUE_ORIGIN
}
