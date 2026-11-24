package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BinOp;

/**
 * A truth that is another value's truth, kept or swapped.
 *
 * <p>{@code Bool.not(p)} is {@code p} denied, and so are {@code p == false} and {@code p != true};
 * {@code p == true} and {@code p != false} are {@code p} itself. Such a value decides nothing of its
 * own. Whatever settles {@code p} settles it, the same way or the other way round, so a reading of
 * either a clause or the ways a value arrives reads {@code operand} and carries the polarity.
 *
 * <p>The denial is the operation's law and not its name ({@link DischargeRules#denies}): the call is
 * one of these because the facts the library's operations are settled by say it answers the denial
 * of its one argument. The comparison is one because one side is a written truth. Nothing else is
 * read through: a helper that happens to answer the same is a helper, and what it answers is its
 * body's to say.
 *
 * <p>Read in the analysis representation, where the operation is kept as the call it is. An
 * {@code if} with written truths in its arms says the same thing in the shape of a fork, and is read
 * as the fork it is by whoever walks forks.
 *
 * @param operand what the truth is the truth of
 * @param denies  whether the truth is {@code operand}'s swapped
 */
public record TruthRestatement(Core operand, boolean denies) {

    /** What {@code value} restates, or null where it is no restatement of another value's truth. */
    public static TruthRestatement of(Core value) {
        Core bare = Core.withoutStanding(value);
        if (bare instanceof Core.PreservedCall call && call.args().size() == 1
                && DischargeRules.denies(call.operation())) {
            return new TruthRestatement(call.args().getFirst(), true);
        }
        if (!(bare instanceof Core.Binary bin) || (bin.op() != BinOp.EQ && bin.op() != BinOp.NE)) {
            return null;
        }
        // An equality against true and a disequality against false keep what the other side
        // states, and the other pair swap it: read off the operator and the literal together.
        boolean equal = bin.op() == BinOp.EQ;
        if (Core.withoutStanding(bin.right()) instanceof Core.Bool truth) {
            return new TruthRestatement(bin.left(), truth.value() != equal);
        }
        return Core.withoutStanding(bin.left()) instanceof Core.Bool truth
                ? new TruthRestatement(bin.right(), truth.value() != equal) : null;
    }
}
