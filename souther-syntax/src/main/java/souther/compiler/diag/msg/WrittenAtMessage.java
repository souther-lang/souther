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
     *
     * <p>So a body that says "here" and then says this reads as a correction of itself, and it stays
     * that way on purpose. The alternative is a second wording per rule — "constructing {@code Pos}
     * here" beside "constructing {@code Pos} in {@code up.mk}" — which moves a rule that holds for
     * every diagnostic into a set that grows with every rule written after {@code HelperInliner}, and
     * nothing would hold it. The rules a message is checked against relate its components to its
     * text; none of them can ask whether a text reads its caret as the place, so a wording written
     * without its variant compiles, ships, and claims a place. One sentence, said off the coordinate,
     * cannot be forgotten.
     *
     * <p>What would make splitting worth it: a message able to declare whether its text reads the
     * caret as the place — a role beside {@code Reported} and {@code Supporting}, held by the build
     * the way the others are. A missing variant would then be refused rather than reviewed, and
     * splitting would cost what it looks like it costs.
     */
    record TheCodeIsWrittenOutOfSight(String declaration) implements WrittenAtMessage, Supporting {}

    /**
     * The same fact where there is no caret: what a label says when the code it is about is in a
     * module this compile has no file for and no coordinate stands in for it.
     *
     * <p>A second wording rather than the one above, because the one above ends by saying what the
     * place under it is — "this is where it was reached from and not where it is" — and there is no
     * place under this one. A label about a clause of a published module points at nothing at all,
     * so a sentence explaining a caret would be explaining something the reader cannot see.
     */
    record TheCodeIsWrittenWhereThisCompileCannotShowIt(String declaration)
            implements WrittenAtMessage, Supporting {}
}
