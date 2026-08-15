package souther.compiler.diag.msg;

/**
 * What a report says about the sources it is reading, rather than about the model written in them.
 */
public sealed interface WrittenAtMessage extends Message {

    /**
     * Said by every report whose caret stands in for code written somewhere this compile has no
     * source for — so the caret is not read as the place the code is.
     *
     * <p>Not written at any of the sites that report one. A body from out of sight is copied with
     * the call site stamped over it, and every rule checked on that copy reports at a coordinate in
     * the caller's file; a sentence each of those sites had to remember is a sentence the next rule
     * added will not say. It is said off the coordinate instead, once, wherever a body is rendered.
     */
    record TheCodeIsWrittenOutOfSight(String declaration) implements WrittenAtMessage, Supporting {}
}
