package souther.compiler.partition;

import java.util.Objects;

/**
 * How the rewrites a plan asks about are looked for: who the row found is for, and how many runs
 * one rewrite may take.
 *
 * <p>Who it is for decides which figures stop it. A row looked for to settle a measure decides
 * whether a rewrite is a gap, so only the measure's own figure for the runs stops it — a figure of
 * the generation stopping it would leave a measurement weaker for how many rows a person is handed,
 * which is no part of what the rows establish. A row looked for to hand a person is one more row of
 * a block, and stops where the block does.
 *
 * <p>The runs come from the measure's policy either way ({@link AdequacyPolicy.OfTheMeasures}): a
 * row handed a person for a rewrite is the row the measure would have found, and looking for it
 * under another figure could hand over a row for a rewrite the measure never found one for.
 *
 * @param use     who a row found is for
 * @param runs    how many runs a search for one rewrite may make
 * @param demands what the bodies ask of the pieces of a string they part, which is where a
 *                string is looked for that a rewrite of what keeps some of the pieces answers
 *                differently on
 */
public record RewriteSearch(For use, int runs, StringDemands demands) {

    public RewriteSearch {
        Objects.requireNonNull(use, "a row a rewrite is told on is looked for on somebody's behalf");
        Objects.requireNonNull(demands, "what the bodies ask of the pieces of a string is asked"
                + " of them, and may be nothing");
        if (runs < 1) {
            throw new IllegalArgumentException("a search runs at least once: " + runs);
        }
    }

    /** A search for a body that asks nothing of the pieces of a string. */
    public RewriteSearch(For use, int runs) {
        this(use, runs, StringDemands.NONE);
    }

    /** Who a row a rewrite is told on is looked for on behalf of. */
    public enum For {
        /** The measure: a row found shows the rewrite is a gap. */
        THE_MEASURE,
        /** A block of rows handed a person, which a row found is one more of. */
        THE_BLOCK
    }
}
