package souther.compiler.types;

/**
 * Which construct the source wrote, said in a way that copying cannot change.
 *
 * <p>A non-recursive helper is expanded at each call, so one construct the author wrote becomes
 * several in the tree that runs. Those copies are separate occurrences — each is emitted, probed and
 * reasoned about on its own — and they are one construct: the author wrote one {@code match}, and
 * writing rows for it twice covers nothing the first set did not. This is what says they are one.
 *
 * <p><b>Named for the source and not for one of its readers.</b> A coverage obligation is derived
 * from some of these, which is what this used to be called after — and a rule read off an
 * application, an application a pass expands, and an arithmetic expression that owes nothing are all
 * one of these too. What every reader shares is the question it answers: which construct of the
 * source is this.
 *
 * <p><b>The identity of a construct the source wrote, and nothing about what is owed for it.</b>
 * Minted where such a construct is read, and carried from there on. Which of them a coverage
 * obligation comes from is a later reader's answer and a narrower set than this: an arithmetic
 * binary expression has one of these and owes nothing, an application has one and owes rows only
 * where a rule is read off it, and a fork owes an arm either way. Read as "a construct a row can be
 * owed for", this value would be one nobody could hand to the constructs that are not.
 *
 * <p><b>Carrying one is not being instrumented and is not being numbered.</b> What a
 * probe copies off the stack is {@link souther.compiler.coverage.SourceOutcome}'s answer, and an
 * arithmetic binary expression has an origin and no number today. A rule about the strings at a
 * position is the other way round from a fork: it owes rows because it divides the position into
 * classes, and no run through it is recorded at all. So the two questions are asked separately, and
 * a reader that took an origin for a probe site would be answering the second with the first.
 *
 * <p>A pass
 * that rewrites one keeps the origin it was given; a pass that turns one construct into several forks
 * derives them with {@link #lowered}, so what a comprehension's guards get is a function of the
 * comprehension rather than of when the lowering ran. Nothing else makes one — an origin minted after
 * expansion would give two copies of one fork two origins, which is the thing this exists to prevent.
 * A record's constructor is public and takes every component, so that last sentence is held against
 * the compiled classes rather than left to be read: what settles an origin is written down, with who
 * calls it.
 *
 * <p>Not a name anything outside one compilation can be matched by. {@code ordinal} is the builder's
 * own count over the source it is reading, and the builder does not take the numbers in the order the
 * constructs are written: a statement guard folds the rest of its block before numbering itself, and
 * a comprehension is numbered after its parts. What identity needs is that the numbering be a
 * function of the source and that two constructs never share one, which it is and they do not.
 * Matching one compilation's obligations against another's is a different question and not one this
 * answers.
 *
 * @param module  the module whose source wrote the construct — what keeps a prelude helper's forks
 *                apart from those of the module expanding it, since each source numbers from zero
 * @param ordinal which construct of that source, by the builder's own count over it
 * @param lowered which fork of that construct, where a lowering makes more than one out of it. Zero
 *                is the construct's own fork, which is every fork an author writes as one
 * @param kind    what the author wrote there. Not part of what tells one construct from another —
 *                the builder takes a fresh ordinal for every construct it reads, so no two origins
 *                share one and nothing here can disagree about a construct two values name. It is
 *                the answer a report needs and the tree that runs no longer holds
 */
public record SourceConstructOrigin(String module, int ordinal, int lowered, SourceConstruct kind) {

    public SourceConstructOrigin {
        // Two spellings of one fact, held together rather than left to agree. `isWritten` is asked
        // by readers that have no use for the kind, and a value answering it one way and carrying a
        // construct the other way is one either reader can be right about.
        if ((ordinal < 0) != (kind == SourceConstruct.NOT_WRITTEN)) {
            throw new IllegalArgumentException(
                    "an origin says both whether a source wrote it and what was written: "
                            + ordinal + " with " + kind);
        }
    }

    /** The construct a source wrote, said as {@code kind}. */
    public static SourceConstructOrigin written(String module, int ordinal, SourceConstruct kind) {
        return new SourceConstructOrigin(module, ordinal, 0, kind);
    }

    /**
     * What a comparison rebuilt for an analysis carries, no source having written it.
     *
     * <p>The invariant-discharge reader turns a preserved call back into a comparison so it can be
     * read as one. That tree is not the tree that runs — coverage numbering refuses a preserved call
     * outright — so nothing here is ever a coverage obligation, and a value that could pass for one
     * would be worse than a value that cannot.
     */
    public static SourceConstructOrigin unwritten() {
        return UNWRITTEN;
    }

    private static final SourceConstructOrigin UNWRITTEN =
            new SourceConstructOrigin("", -1, 0, SourceConstruct.NOT_WRITTEN);

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
    public SourceConstructOrigin lowered(int part) {
        if (lowered != 0) {
            throw new IllegalStateException(
                    "a lowered fork cannot be lowered again: " + this + " part " + part);
        }
        // The kind comes along. A guard of a comprehension is a fork of that comprehension, and a
        // fork that arrived saying it was written as something else would be the construct this
        // whole value exists to keep hold of, lost one lowering in.
        return new SourceConstructOrigin(module, ordinal, part + 1, kind);
    }
}
