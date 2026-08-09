package souther.compiler.fmt;

import java.util.List;

/**
 * A canonical form as it was laid out: the text, and the decisions the layout took to arrive at it.
 *
 * <p>{@link Doc} is the program — what may break where, and how far in. This is what running it
 * produced. The two are kept apart because the text is a projection: a group written down the page
 * because it did not fit and one written down the page because it holds a forced break are the same
 * characters, and a reader given only the characters has to lay the document out again to tell them
 * apart.
 *
 * <p>Not a record of how the layout was computed. Nothing here says that {@code fits} was called or
 * that a nesting was entered; those are the mechanism and they change when the code is rearranged.
 * What is kept is what the layout realized, which is what the canonicalization rules are about.
 */
record Layout(String text, List<GroupDecision> decisions, java.util.Map<Place, Span> spans) {

    Layout {
        decisions = List.copyOf(decisions);
        spans = java.util.Map.copyOf(spans);
    }
}
