package souther.compiler.coverage;

/**
 * What this compile's own recording has of one run.
 *
 * <p>Two answers and not an account that may be empty. A run recorded under a numbering and a run
 * nothing was recording are different facts about a row: the first says where it went, and the
 * second says nobody was watching. Written as one empty account, the second reads as a row that
 * passed nowhere — which is what a row shown to miss every arm looks like, and is the opposite of
 * what happened.
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

    /** Nothing was recording. The classes the row ran through were generated without the calls that
     *  would have written anything down, so there is nothing here and nothing went nowhere. */
    record NotRecording() implements RunRecord {}
}
