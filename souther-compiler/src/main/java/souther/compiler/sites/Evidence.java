package souther.compiler.sites;

/**
 * What read a fact.
 *
 * <p>Carried because two facts of the same shape are not worth the same. What a declaration says is
 * true of every use of it and is there before any body compiles; what a check read is true of one
 * elaboration of one expression, and one authored expression has as many of those as there are calls
 * of the helper it sits in. A reader holding only the type would have to decide which of the two it
 * had by remembering where it asked.
 *
 * <p>Not two sources competing to answer one question. They answer about different things, and one
 * reading may hold both — which is why this is on the fact and not a choice made once for a whole
 * snapshot.
 *
 * <p>Which declaration a declared fact was read off is not here. Nothing works it out, so nothing
 * would be saying it: the walk answers a type, and where a step of it came from would be a second
 * thing to keep true. It is a component to add when something computes one.
 */
public sealed interface Evidence {

    /**
     * Read off declarations the author wrote, by the one walk that answers that question.
     *
     * <p>True whether or not any body compiles, which is what makes it the evidence an editor gets
     * while a line is half written.
     */
    record Declared() implements Evidence {}
}
