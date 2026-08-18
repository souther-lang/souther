package souther.compiler.types;

/**
 * Which construct of the language a coverage obligation was written as.
 *
 * <p>The other half of {@link CoverageOrigin}. That says which construct this is, so that copies of
 * one fork stay one obligation; this says what the author wrote there. Both are answers about the
 * source, and neither can be read off the tree that runs: {@code guard} is sugar for {@code if}
 * (ADR-0020), a list comprehension is rewritten before Core exists, and by the time coverage is
 * numbered one node stands for all three. A reader asking what to call the construct, or what one of
 * its outcomes means, is asking about the source, so the answer travels from where the source was
 * read rather than being worked out again from the shape it was lowered to.
 *
 * <p>Settled where the construct is read and carried from there. Nothing derives one later — every
 * rewrite between the AST and Core copies the origin it was given, so this arrives at a report
 * unchanged however many times a helper holding the construct was expanded.
 */
public enum CoverageConstruct {

    /** {@code if c then a else b}, and {@code if T(v) as x then a else …}. */
    IF,

    /**
     * {@code guard c else x}, and {@code guard T(v) as x else …}.
     *
     * <p>An {@code if} by the time anything runs, and not one to a reader: the author wrote one arm
     * of it and the compiler supplied the other, which is the rest of the block.
     */
    GUARD,

    /**
     * A list comprehension's guard — {@code [e | c]}.
     *
     * <p>One construct however many conditions it lists. Each becomes a fork of its own, derived
     * from this one by {@link CoverageOrigin#lowered}, so the guards of one comprehension are told
     * apart without any of them being taken for a construct the author wrote separately.
     */
    COMPREHENSION,

    /** {@code match}. */
    MATCH,

    /**
     * A binary expression — a comparison, a conjunction, an arithmetic operation, a concatenation.
     *
     * <p>What was written, and not what was made of it. Only a comparison inside a fork's condition
     * is ever numbered, and whether this one was is {@link souther.compiler.coverage.SourceOutcome}'s
     * answer rather than this one's: {@code a + b} is as much a binary expression the source wrote as
     * {@code a > b} is, and naming the construct after the use the analysis puts a few of them to
     * would make this value say something untrue of every arithmetic node in every body.
     */
    BINARY,

    /**
     * No source wrote it.
     *
     * <p>What {@link CoverageOrigin#unwritten} carries. A comparison rebuilt for an analysis is a
     * binary expression, and giving it {@link #BINARY} would make it a value that passes for a
     * coverage obligation — which is the thing that origin exists not to be. Named here so that a
     * switch needing a construct the author wrote has somewhere to refuse it.
     */
    NOT_WRITTEN;

    /**
     * What a sentence in the reader's language calls this.
     *
     * <p>A key and not a word. The walk that found the construct has no reader, so it has no language
     * to name one in; what it can say is which construct it was, and the catalog says the rest.
     *
     * @throws IllegalStateException where the construct is not one a fork of a body is written as.
     *                               A {@code match} has arms rather than a line, a comparison is
     *                               inside a fork rather than being one, and nothing wrote the last
     */
    public souther.compiler.diag.Localizable said() {
        return switch (this) {
            case IF -> souther.compiler.diag.Localizable.of("construct.if");
            case GUARD -> souther.compiler.diag.Localizable.of("construct.guard");
            case COMPREHENSION -> souther.compiler.diag.Localizable.of("construct.comprehension");
            case MATCH, BINARY, NOT_WRITTEN -> throw new IllegalStateException(
                    "not a fork of a body: " + this);
        };
    }
}
