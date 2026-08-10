package souther.compiler.types;

/**
 * The fork a coverage obligation was written as, said in a way that copying cannot change.
 *
 * <p>A non-recursive helper is expanded at each call, so one fork the author wrote becomes several
 * forks in the tree that runs. Those copies are separate occurrences — each is emitted, probed and
 * reasoned about on its own — and they are one obligation: the author wrote one {@code match}, and
 * writing rows for it twice covers nothing the first set did not. This is what says they are one.
 *
 * <p>Minted where a source construct that can carry arms is read, and carried from there on. A pass
 * that rewrites a fork keeps the origin it was given; a pass that turns one construct into several
 * forks derives them with {@link #lowered}, so what a comprehension's guards get is a function of the
 * comprehension rather than of when the lowering ran. Nothing else makes one — an origin minted after
 * expansion would give two copies of one fork two origins, which is the thing this exists to prevent.
 *
 * <p>Not a stable name across revisions. {@code ordinal} counts the constructs of one source in the
 * order they are read, so writing a fork above another moves the one below it. What it is for is
 * holding copies together within one compilation, and matching one compilation's obligations against
 * another's is not a question it answers.
 *
 * @param module  the module whose source wrote the construct — what keeps a prelude helper's forks
 *                apart from those of the module expanding it, since each source numbers from zero
 * @param ordinal which construct of that source, in the order they were read
 * @param lowered which fork of that construct, where a lowering makes more than one out of it. Zero
 *                is the construct's own fork, which is every fork an author writes as one
 */
public record CoverageOrigin(String module, int ordinal, int lowered) {

    /** The fork a source construct was written as. */
    public static CoverageOrigin written(String module, int ordinal) {
        return new CoverageOrigin(module, ordinal, 0);
    }

    /**
     * One of the forks a lowering makes out of this construct, numbered by the part of the construct
     * it came from — a list comprehension's guards by their place in the list.
     *
     * <p>Derived rather than minted, so the same guard of the same comprehension answers the same
     * whether the lowering runs before an expansion copies it or after.
     *
     * @throws IllegalStateException where this is already one of a construct's lowered forks. One
     *                               level is all any lowering needs, and a second would fold two
     *                               different parts into one number
     */
    public CoverageOrigin lowered(int part) {
        if (lowered != 0) {
            throw new IllegalStateException(
                    "a lowered fork cannot be lowered again: " + this + " part " + part);
        }
        return new CoverageOrigin(module, ordinal, part + 1);
    }
}
