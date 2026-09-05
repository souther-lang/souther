package souther.compiler.inputs;

import java.util.List;

/**
 * Two readings of one question that disagree about what the author wrote it short of.
 *
 * <p>What a question stands for is the parts of the rule that raised it, in the order they were
 * written, and a document says it as that. So two accounts of one question are two accounts of one
 * thing, and a difference between them is not something to put together: taking either would
 * publish a precedence nothing in the model decides, and joining them would say the author wrote
 * something they did not.
 *
 * <p>Not an argument somebody got wrong, which is what an {@link IllegalArgumentException} out of a
 * fold reads as. Both accounts were produced by this compiler from one model, so what is wrong is
 * the state they were read out of and not what a caller handed over — and the type says which.
 */
public final class TwoAccountsOfOneQuestion extends IllegalStateException {

    private static final long serialVersionUID = 1L;

    public TwoAccountsOfOneQuestion(StandingQuestion.Exact.Fact question,
                                    List<BlockReason.AboutARule> one,
                                    List<BlockReason.AboutARule> other) {
        super("two readings of " + question + " disagree about what the author wrote it short of: "
                + one + " and " + other);
    }
}
