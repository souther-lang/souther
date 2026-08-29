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
     * What a run of rules with no line at one position leaves it with, or null where it holds
     * none.
     *
     * <p><b>A stop ahead of a rule read to the end, and never the first of the list.</b> Either
     * keeps the position from completing as one the model draws no line through, and they are not
     * alike in anything else: one is a limit somebody can lift and the other is what the model
     * says. Taken in the order the rules happen to be in, which of the two a position came out
     * under turned on which clause its author wrote first.
     */
    static LeftAtThePosition of(Iterable<souther.compiler.inputs.RuleWithoutALine> rules) {
        LeftAtThePosition out = null;
        for (souther.compiler.inputs.RuleWithoutALine rule : rules) {
            out = outranking(out, of(rule.why()));
        }
        return out;
    }

    /**
     * Of two, the one that outranks — and the first where they rank alike.
     *
     * <p>The one priority, written once, because more than one reading answers about a position and
     * their answers have to be put together. A reading that stopped outranks a rule read to the
     * end: what such a rule states is known, and what a stop leaves is not, so a position where
     * both happened is one somebody can still do something about. Written per phase, the phases
     * disagreed — the input reading's rule read to the end hid a stop in the body, and a stop in
     * the input reading was hidden by nothing at all.
     */
    static LeftAtThePosition outranking(LeftAtThePosition first, LeftAtThePosition second) {
        if (first == null) {
            return second;
        }
        if (second == null) {
            return first;
        }
        return first instanceof AReadingStopped || !(second instanceof AReadingStopped)
                ? first : second;
    }

    /**
     * Which of the two {@code why} is, asked once.
     *
     * <p>A reason a rule reading stopped on is in both capabilities — it is a stop, and it is a rule
     * with no line — and a stop is what it is here: what such a rule would have divided the position
     * by is exactly the part nobody read. So the stop is asked first, and the arms are the whole of
     * {@link BlockReason.RuleWithoutLineReason} between them.
     *
     * <p>Which is what this takes, and not every reason there is. What a position is left with comes
     * from a rule about it that came to no line, so a reason of another kind has no rule here to be
     * the account of — a shortfall about a rule no reading claimed says nothing about a line, and
     * nothing here would know which of the two arms to put it under.
     */
    static LeftAtThePosition of(BlockReason.RuleWithoutLineReason why) {
        return switch (why) {
            case BlockReason.RuleReadingStopped stopped -> new AReadingStopped(stopped);
            case BlockReason.ReadToEndWithoutLine read -> new ARuleWithNoLine(read);
        };
    }
}
