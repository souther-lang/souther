package souther.compiler.types;

/**
 * Which rule a source wrote — a block, told from every other block that source wrote.
 *
 * <p>Minted where the syntax is read and carried by every copy of it, which is what makes it an
 * identity. A rule handed to a function parameter decides the arms of the fork that applies it, so
 * two call sites handing in two rules are two things to cover and two handing in one are one. What
 * settles which of those it is has to survive the body being spliced.
 *
 * <p>Not a position. A position says where this compile put a node, and a copy of a body a reader
 * cannot open is stamped with the call site that spliced it — so two rules written in one library
 * helper come to one position, and one rule copied to two call sites comes to two. Read as identity,
 * the first counts two rules as one and reports a rule nothing exercised as covered; the second asks
 * an author for a row establishing what another row already does.
 *
 * <p>Beside {@link SourceConstructOrigin} and minted the same way, because it answers the same kind of
 * question about a different construct. They are counted apart: what numbers one is not what numbers
 * the other, and a construct is one or the other and never both.
 *
 * <p>Counted within the owner and not over the file, for the reason {@link CoverageOrigin} gives:
 * a number counted over everything a source wrote moves when anything written before it does.
 *
 * @param owner   what wrote the block. Null exactly for {@link #unwritten}
 * @param ordinal which block of that owner, by the builder's own count over it
 */
public record RuleOrigin(WrittenOwner owner, int ordinal) {

    public RuleOrigin {
        if ((owner == null) != (ordinal < 0)) {
            throw new IllegalArgumentException("a rule says whether a source wrote it, and what it"
                    + " was counted within: " + owner + " with " + ordinal);
        }
    }

    /** The block {@code owner} wrote, counted as {@code ordinal} among the ones written there. */
    public static RuleOrigin written(WrittenOwner owner, int ordinal) {
        return new RuleOrigin(owner, ordinal);
    }

    /** The module whose source wrote the block, or null where nobody wrote it. Asked of the owner,
     *  which is what knows. */
    public String module() {
        return owner == null ? null : owner.module();
    }

    /**
     * What a block a pass built carries, no source having written it.
     *
     * <p>Not an identity, and asked for as one it would make every such block the same rule. What
     * stands where a pass built a block is what the author wrote there — a name, most often — and it
     * is that which says which rule this is.
     */
    public static RuleOrigin unwritten() {
        return new RuleOrigin(null, -1);
    }

    /** Whether a source wrote the block this names. */
    public boolean isWritten() {
        return owner != null;
    }
}
