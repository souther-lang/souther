package souther.compiler.coverage;

/**
 * What this compile's own recording has of one run.
 *
 * <p>Two answers and not an account that may be empty. A run that was recorded and a row there is
 * no account of are different facts: the first says where it went, and the second says nothing was
 * written down. Written as one empty account, the second reads as a row that passed nowhere — which
 * is what a row shown to miss every arm looks like, and is the opposite of what happened.
 *
 * <p>Said here rather than left to a reader. A number a run leaves behind means a place under the
 * numbering that handed it out ({@link SiteNumbering#align}), so an account has to say which
 * numbering it is of; a compile that recorded nothing has no numbering to name, and an account
 * naming one it was never under is the mistake that alignment exists to refuse.
 */
public sealed interface RunRecord {

    /** The run was recorded, and this is what it left behind. */
    record Recorded(Observation seen) implements RunRecord {

        public Recorded {
            if (seen == null) {
                throw new IllegalArgumentException("a recorded run is a run that was recorded");
            }
        }
    }

    /**
     * No account of the run was taken.
     *
     * <p>Said as the absence rather than as its reason. There are two of those and a reader here
     * acts on neither: the classes the row ran through may have been generated without the calls
     * that write a run down, or the row may have stopped somewhere the snapshot is not reached —
     * and a name asserting the first would be asserting it of the second. What every reader of this
     * needs is that there is no account, which is not the same as an account of a run that went
     * nowhere.
     */
    record NoAccount() implements RunRecord {}
}
