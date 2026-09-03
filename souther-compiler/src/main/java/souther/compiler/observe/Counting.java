package souther.compiler.observe;

import souther.compiler.coverage.RunRecord;

/**
 * What this compile's own counting read of one row's evaluation.
 *
 * <p>Both numbers are about code the emitter counted into, which is what this compile generated and
 * nothing else. That is the whole of what they cover and it is not the same as the application: a
 * fixture applies the helpers it names before the behavior is reached, so a row that never applied
 * the behavior can still have spent counted points, and a row applied through something this compile
 * did not generate spends none inside the application while its fixtures spend what they spend.
 * {@link Applied} is what says which of those a row is.
 *
 * <p>A reading and no reading are different values here rather than one value a reader has to
 * qualify. An evaluation that was given up on is still running when the outcome is written, and a
 * count taken from it would be some of what it spent rather than what it spent — so nothing is
 * taken, and {@link Unread} says that. Writing zero would have said the row passed no counted point,
 * which is what a body with no loop in it does, and the two would be one number again.
 */
public sealed interface Counting {

    /**
     * The counting was read, and this is what it said.
     *
     * <p>{@link #steps} is what the row cost in the unit it is held to, so a build can see how much
     * of the budget its rows use before one of them reaches it — the only way to set the budget from
     * evidence rather than by guessing. Zero says no counted point was passed, and says only that.
     *
     * <p>{@link #recorded} is what the row was seen to do, where anything was watching — the sites it
     * went through and the ways its comparisons came out. Whether anything was is a property of the
     * compile rather than of the row, and it is one of that value's two answers rather than an empty
     * account: a row nobody watched did not pass nowhere.
     *
     * <p>The steps and the recording are both read here and are different questions. A compile that
     * counts steps records nothing unless it also emitted the calls that write a run down, so a
     * count that came back is not evidence that a run did.
     */
    record Read(long steps, RunRecord recorded) implements Counting {

        public Read {
            if (recorded == null) {
                throw new IllegalArgumentException(
                        "a row says what was recorded of it, or that nothing was");
            }
        }
    }

    /**
     * The counting was not read.
     *
     * <p>What the row would have cost is not known here and is not zero. A reader that needs a number
     * has none; a reader counting what rows covered has nothing this row can add, and that the row
     * was left undecided is said where the row is reported ({@link Incompleteness}).
     */
    record Unread() implements Counting {}
}
