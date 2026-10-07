package souther.compiler.partition;

import souther.compiler.coverage.CoverageSites;

import java.util.List;

/**
 * What looking for a row that goes further found out, where it took a row no further than a guard.
 *
 * <p>Beside the row and never in place of it. The row the search found holds every pin, so it is
 * the answer to what it was composed for whatever this says; what this says is why the row a
 * reader is handed stops where it does. And not part of what the row is: two rows written the same
 * way are one line whatever was tried in looking past it ({@link ComposedRow}), so this travels
 * with the row and is never what tells one row from another.
 *
 * <p><b>Every way past the guard, and what each came to.</b> A way a search was made for, a way no
 * search could be made for, and a way the runs ran out in front of are three different pieces of
 * news, and the word of the last search is none of them for the others. Held as one reason, a
 * guard nothing here can hold a row to and a guard the model lets no row past would read alike —
 * and the second is about the model while the first is about this compiler.
 */
public sealed interface RepairShortfall {

    /** The guard the row stops at, as the arm a run it refuses leaves by. */
    CoverageSites.ArmSite refused();

    /**
     * Each way past the guard was looked at and none of them gave a row that goes on.
     *
     * <p>In the order the reading of the body reached them, which is the model's order and not the
     * order they were looked for in: the search tries the ways that ask least of the row first,
     * which is a guess about where a row is, and a report that followed it would change with the
     * guess.
     *
     * @param refused the guard, as the arm a run it refuses leaves by
     * @param ways    what each way past it came to; none where the reading of the body could not
     *                write the ways down
     */
    record NoWayPast(CoverageSites.ArmSite refused, List<WayPast> ways)
            implements RepairShortfall {

        public NoWayPast {
            ways = List.copyOf(ways);
        }
    }

    /**
     * The row furthest in stops at a guard a row was already taken past.
     *
     * <p>Each guard is looked past once, because a row taken past one guard and stopped at the
     * next can be composed again into a row stopped at the first, and looking again would go round.
     * What the row is held to keeps every comparison a way past the earlier guard asked for, and
     * still a comparison the earlier row was only seen doing is not held — so this is the row
     * coming back to a guard and nothing being tried there a second time.
     *
     * @param refused the guard, as the arm a run it refuses leaves by
     */
    record BackAtAGuardLookedPast(CoverageSites.ArmSite refused) implements RepairShortfall {}

    /** What one way past a guard came to. */
    sealed interface WayPast {

        /**
         * Looked for, and the search composed nothing that goes this way.
         *
         * <p>What the search came to in its own words, with what it found out beside them. A word
         * this compiler fell short with and a word the model settles stay the words they are —
         * that nothing here could compose a value is not that the rules leave none.
         */
        record Searched(CameToNothing came) implements WayPast {}

        /**
         * Looked for until the runs ran out, with nothing found before they did.
         *
         * @param came   what the search had come to when it stopped
         * @param figure what ran out
         */
        record CutShort(CameToNothing came, CompositionBudget figure) implements WayPast {}

        /** Not looked for: the runs had run out before the search for it began. */
        record Untried(CompositionBudget figure) implements WayPast {}

        /** Not looked for, because nothing here can hold a row to it. */
        record NotSearchable(Barrier why) implements WayPast {}
    }

    /** Why a way past a guard is one no search can be made for. */
    enum Barrier {

        /**
         * A part of it is an arm, or a comparison no border offers a point on the side the way
         * asks for. What a search holds a row to is a point of a border, and there is none here.
         */
        NOTHING_HOLDS_A_ROW_TO_IT,

        /**
         * Holding the row to it would compose afresh a parameter the row writes as the value the
         * model states. That value is the author's, and what it does to the body is what the row
         * says about it.
         */
        IT_WOULD_REWRITE_A_STATED_VALUE,

        /**
         * The row was already seen doing every part of it, and stopped at the guard all the same.
         * There is nothing left to ask of a row, so the ways the reading wrote down are not every
         * way the guard has.
         */
        THE_ROW_ALREADY_DOES_ALL_OF_IT
    }
}
