package souther.runtime;

/**
 * Where a runtime operation tells whoever is holding an evaluation to an allowance that it has done
 * one more piece of work, handed in by the code that called it.
 *
 * <p>The operation holds no allowance of its own and does not know what it is counted in. What an
 * evaluation may spend, and whether whoever it runs for has given up on it, belongs to the
 * evaluation; the operation only passes the point, and the checkpoint stops it by throwing where the
 * evaluation is over. What it throws comes out of the operation as it is.
 *
 * <p>An operation that takes one passes it once a time round every loop whose count turns on a value
 * it was handed — the characters of a text, the elements of a collection, the copies of a repeat, the
 * comparisons of a sort — and, where it hands work to the text rules of 199x-notation, those rules
 * ask it as often as they say they ask. Between two passes it goes over no more of a value than one
 * of those: what it does there is a lookup, a step of a trie, or a loop with a fixed most. What the
 * platform does in one operation to make an answer, such as growing the room it is written into or
 * copying it out into a string, is not passed inside.
 *
 * <p>One call the operation cannot pass inside — a {@code BigInteger} multiplied, a {@code BigDecimal}
 * divided — is paid for before it is made, by {@link #spend} of the pieces of work it stands for.
 * That count is worked out from how large the operands are as they are held, in words of the
 * number and not in time, so it is the same on every machine; and it is not worked out from a
 * scale, since a value one digit long at a scale of a million is held in a few words and the
 * language does not let it cost more for that. What is paid before the call stops it from starting
 * where the evaluation could not afford it, and an evaluation given up on while the call runs stops
 * at the next pass after it.
 *
 * <p>Generated code hands one in only where it is evaluated. A class that ships calls the same
 * operation without one, and the operation then does what it did before there was a checkpoint to
 * pass.
 */
@FunctionalInterface
public interface WorkCheckpoint {

    /** {@code pieces} pieces of work done at once; throws where the evaluation they are done for is
     *  over, or cannot afford them. {@code pieces} is never negative. */
    void spend(long pieces);

    /** One more piece of work done. */
    default void pass() {
        spend(1);
    }

    /** The checkpoint of work nobody is holding to an allowance: passing it does nothing. */
    WorkCheckpoint NONE = pieces -> { };
}
