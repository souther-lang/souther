package souther.compiler.partition;

import souther.compiler.inputs.BlockReason;

/**
 * What a position with no evidence is left with, told apart by whose account it is.
 *
 * <p>Two things keep a position from being one the model draws no line through, and they are
 * opposite sentences. A reading stopped here, so what the model says is not known; or every reading
 * ran to the end and a rule states something the readings turn into no line. The first is a limit
 * somebody can lift and the second is what the model says.
 *
 * <p><b>Told apart here rather than downstream.</b> The distinction is one this compiler makes in
 * four places — whether a measure could not be made or the model states this, whether a question
 * stands or is answered, which word a claim is annotated with — and each of them used to work it
 * out from where the evidence had come from rather than from what it says. That was sound while a
 * position could only be left with a stop; a rule read from end to end that draws no line reaches
 * the same slot, and every one of those derivations went on answering as though it had not.
 *
 * <p>So the slot is a sum and not a {@link BlockReason}. A caller holding one of these has already
 * been told which of the two it is, and cannot spell the question a fifth way.
 */
public sealed interface LeftAtThePosition {

    /** Why, whichever of the two it is — for a reader that wants the reason and not the account. */
    BlockReason why();

    /**
     * A reading stopped, so what is written here is not known to have been read.
     *
     * <p>Whichever reading: the walk that reaches into what a position holds, the reading of which
     * values may stand there, or the reading of ends stopping on a rule. What they leave is the
     * same — the position may yet be divided by what nobody managed to read.
     */
    record AReadingStopped(BlockReason.ReadingStopReason why) implements LeftAtThePosition {

        public AReadingStopped {
            if (why == null) {
                throw new IllegalArgumentException("a reading that stopped says why");
            }
        }
    }

    /**
     * A rule was read from end to end and draws no line here.
     *
     * <p>Nothing is missing. The rule relates this position to another, or cuts a quantity it does
     * not appear in, or draws its line where that quantity never runs — each of them a fact about
     * the rule, and each of them a reason the position has no class of its own that a row could be
     * written for.
     *
     * <p>Still not an absence. The model states something here, so a verdict that the model divides
     * the position no way would be saying what the declaration two tokens away denies.
     */
    record ARuleWithNoLine(BlockReason.ReadToEndWithoutLine why) implements LeftAtThePosition {

        public ARuleWithNoLine {
            if (why == null) {
                throw new IllegalArgumentException("a rule with no line here says why it has none");
            }
        }
    }

    /**
     * Which of the two {@code why} is, asked once.
     *
     * <p>A reason a rule reading stopped on is in both capabilities — it is a stop, and it is a rule
     * with no line — and a stop is what it is here: what such a rule would have divided the position
     * by is exactly the part nobody read. So the stop is asked first, and the arms are the whole of
     * {@link BlockReason} between them.
     */
    static LeftAtThePosition of(BlockReason why) {
        return switch (why) {
            case BlockReason.ReadingStopReason stopped -> new AReadingStopped(stopped);
            case BlockReason.ReadToEndWithoutLine read -> new ARuleWithNoLine(read);
        };
    }
}
