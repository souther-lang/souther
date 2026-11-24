package souther.compiler.coverage;

import souther.compiler.types.SourceConstruct;

import java.util.Locale;

/**
 * The short word a table prints and a document writes for one way through a construct.
 *
 * <p>The word and not the pair it is made from. Two constructs may be written differently and have
 * their ways through them called alike — an attempted construction under an {@code if} and under a
 * {@code guard} are both {@code constructed} and {@code else} — and two outcomes may be called alike
 * where they differ. What a reader is told is the word, so whether two ways through a construct
 * read alike is asked of this and of nothing finer: a question asked of the pair parts what the
 * word does not, and leaves two lines a reader cannot tell apart.
 *
 * <p>Written off {@link OutcomeName}, which is the pair already settled, so a construct or an
 * outcome added to the language reaches this as a name it has to be given a word for rather than as
 * a case that falls through.
 */
public final class ArmWord {

    /**
     * The word for an outcome of a construct.
     *
     * <p>An arm is a construct and an outcome whether or not a run through it is recorded, and a
     * sibling an arm is rewritten as is often one nothing records. Every reader comes here, so an
     * arm a rewrite names and the same arm a branch line names are one word.
     */
    public static String of(SourceConstruct construct, SourceOutcome outcome) {
        return switch (outcome) {
            case SourceOutcome.Matched matched -> "case " + matched.named();
            // The word the author put the departure under, and the clause where they named one. The
            // name of this outcome is `departure`, which says what happened rather than what is
            // written there; a reader of a table is looking at the file.
            case SourceOutcome.Failed(SourceOutcome.FailedBy.Construction(var clause)) ->
                    clause.map(c -> "else " + c).orElse("else");
            case SourceOutcome.Compared(var op) -> op.toString();
            case SourceOutcome.Held _, SourceOutcome.Failed _ ->
                    OutcomeName.of(construct, outcome).name().toLowerCase(Locale.ROOT);
        };
    }

    private ArmWord() {}
}
