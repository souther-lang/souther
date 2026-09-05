package souther.compiler.types;

/**
 * The construct a coverage obligation was written as, said in a way that copying cannot change.
 *
 * <p>A non-recursive helper is expanded at each call, so one fork the author wrote becomes several
 * forks in the tree that runs. Those copies are separate occurrences — each is emitted, probed and
 * reasoned about on its own — and they are one obligation: the author wrote one {@code match}, and
 * writing rows for it twice covers nothing the first set did not. This is what says they are one.
 *
 * <p>Minted where a source construct a row can be owed for is read, and carried from there on. A pass
 * that rewrites one keeps the origin it was given; a pass that turns one construct into several forks
 * derives them with {@link #lowered}, so what a comprehension's guards get is a function of the
 * comprehension rather than of when the lowering ran. Nothing else makes one — an origin minted after
 * expansion would give two copies of one fork two origins, which is the thing this exists to prevent.
 * A record's constructor is public and takes every component, so that last sentence is held against
 * the compiled classes rather than left to be read: what settles an origin is written down, with who
 * calls it.
 *
 * <p>Not a name anything outside one compilation can be matched by. {@code ordinal} is the builder's
 * own count over what {@link #owner} names, and the builder does not take the numbers in the order
 * the constructs are written: a statement guard folds the rest of its block before numbering itself,
 * and a comprehension is numbered after its parts. What identity needs is that the numbering be a
 * function of the source and that two constructs never share one, which it is and they do not.
 * Matching one compilation's obligations against another's is a different question and not one this
 * answers.
 *
 * <p>Counted within the owner and not over the file. A count over the file makes the number a
 * function of everything written before it there, so editing one definition renumbers the
 * constructs of every one after it — and an identity that moves for an edit nothing about it can
 * see is not one.
 *
 * @param owner   what wrote the construct: the declaration, the stated behavior, the body, or the
 *                source's rows for a behavior. Null exactly for {@link #unwritten}
 * @param ordinal which construct of that owner, by the builder's own count over it
 * @param lowered which fork of that construct, where a lowering makes more than one out of it. Zero
 *                is the construct's own fork, which is every fork an author writes as one
 * @param kind    what the author wrote there. Not part of what tells one construct from another —
 *                the builder takes a fresh ordinal for every construct it reads, so no two origins
 *                share one and nothing here can disagree about a construct two values name. It is
 *                the answer a report needs and the tree that runs no longer holds
 */
public record CoverageOrigin(WrittenOwner owner, int ordinal, int lowered, CoverageConstruct kind) {

    public CoverageOrigin {
        // Three spellings of one fact, held together rather than left to agree. `isWritten` is asked
        // by readers that have no use for the kind, and a value answering it one way and carrying a
        // construct the other way is one either reader can be right about. The owner goes with them:
        // a number counted within nothing addresses nothing.
        if ((ordinal < 0) != (kind == CoverageConstruct.NOT_WRITTEN)) {
            throw new IllegalArgumentException(
                    "an origin says both whether a source wrote it and what was written: "
                            + ordinal + " with " + kind);
        }
        if ((owner == null) != (ordinal < 0)) {
            throw new IllegalArgumentException(
                    "an origin a source wrote says what it was counted within: "
                            + owner + " with " + ordinal);
        }
    }

    /** The construct {@code owner} wrote, counted as {@code ordinal} among the ones written there,
     *  and said as {@code kind}. */
    public static CoverageOrigin written(WrittenOwner owner, int ordinal, CoverageConstruct kind) {
        return new CoverageOrigin(owner, ordinal, 0, kind);
    }

    /** The module whose source wrote the construct, or null where nobody wrote it. Asked of the
     *  owner, which is what knows. */
    public String module() {
        return owner == null ? null : owner.module();
    }

    /**
     * What a comparison rebuilt for an analysis carries, no source having written it.
     *
     * <p>The invariant-discharge reader turns a preserved call back into a comparison so it can be
     * read as one. That tree is not the tree that runs — coverage numbering refuses a preserved call
     * outright — so nothing here is ever a coverage obligation, and a value that could pass for one
     * would be worse than a value that cannot.
     */
    public static CoverageOrigin unwritten() {
        return UNWRITTEN;
    }

    private static final CoverageOrigin UNWRITTEN =
            new CoverageOrigin(null, -1, 0, CoverageConstruct.NOT_WRITTEN);

    /** Whether a source wrote the construct this names. False only for {@link #unwritten}. */
    public boolean isWritten() {
        return ordinal >= 0;
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
        // The kind comes along. A guard of a comprehension is a fork of that comprehension, and a
        // fork that arrived saying it was written as something else would be the construct this
        // whole value exists to keep hold of, lost one lowering in.
        return new CoverageOrigin(owner, ordinal, part + 1, kind);
    }
}
