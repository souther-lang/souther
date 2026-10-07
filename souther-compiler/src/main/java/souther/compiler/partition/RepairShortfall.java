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
 * <p><b>For the requirement it was looked for, and not for the row.</b> One row can answer several
 * requirements, and the search past the guard was made for one of them — with that requirement's
 * pins held, so what it came to is about that requirement. Carried here, two stops on one offered
 * row each still say whose they are.
 *
 * <p><b>What the guard came to, and every way past it.</b> A guard whose condition never comes out
 * the way the block goes on, one whose ways past this compiler could not write down, and one whose
 * ways were each looked at are different pieces of news, and so is each way: a way a search was
 * made for, a way the runs ran out on and a way no search could be made for. Held as one reason,
 * a guard nothing here can hold a row to and a guard the model lets no row past would read alike —
 * and the second is about the model while the first is about this compiler.
 *
 * @param soughtFor what the search that took the row this far was for
 * @param refused   the guard, as the arm a run it refuses leaves by
 * @param came      what looking past the guard came to
 */
public record RepairShortfall(List<Generator.Purpose> soughtFor, CoverageSites.ArmSite refused,
                              AtTheGuard came) {

    public RepairShortfall {
        soughtFor = List.copyOf(soughtFor);
        if (soughtFor.isEmpty()) {
            throw new IllegalArgumentException("a row is looked past a guard for something");
        }
    }

    /** What looking past one guard came to. */
    public sealed interface AtTheGuard {

        /**
         * Each way past the guard was looked at and none of them gave a row that goes on.
         *
         * <p>In the order the reading of the body reached them, which is the model's order and not
         * the order they were looked for in: the search tries the ways that ask least of the row
         * first, which is a guess about where a row is, and a report that followed it would change
         * with the guess.
         *
         * @param ways what each way past it came to, one apiece and never none: a guard with no way
         *             past it is {@link NoWayGoesPast}
         */
        record NoWayPast(List<WayPast> ways) implements AtTheGuard {

            public NoWayPast {
                ways = List.copyOf(ways);
                if (ways.isEmpty()) {
                    throw new IllegalArgumentException("a guard looked past way by way has a way;"
                            + " one with none is a guard no row goes past");
                }
            }
        }

        /**
         * The guard's condition never comes out the way the block goes on, so no row goes past it.
         *
         * <p>What the reading of the body settles, and not a search falling short: every way the
         * condition comes out was written down, and none of them is that way.
         */
        record NoWayGoesPast() implements AtTheGuard {}

        /**
         * The ways the guard's condition comes out the way the block goes on are not something the
         * reading of the body could write down, so none of them was looked for.
         *
         * <p>This compiler's shortfall and never the model's word: the guard may well let rows
         * past.
         */
        record WaysNotRead() implements AtTheGuard {}

        /**
         * The row furthest in stops at a guard a row was already taken past.
         *
         * <p>Each guard is looked past once, because a row taken past one guard and stopped at the
         * next can be composed again into a row stopped at the first, and looking again would go
         * round. What the row is held to keeps every comparison a way past the earlier guard asked
         * for, and still a comparison the earlier row was only seen doing is not held — so this is
         * the row coming back to a guard and nothing being tried there a second time.
         */
        record BackAtAGuardLookedPast() implements AtTheGuard {}
    }

    /** What one way past a guard came to. */
    public sealed interface WayPast {

        /**
         * Looked for, and the search composed nothing that goes this way.
         *
         * <p>What the search came to in its own words, with what it found out beside them. A word
         * this compiler fell short with and a word the model settles stay the words they are —
         * that nothing here could compose a value is not that the rules leave none.
         */
        record Searched(CameToNothing came) implements WayPast {}

        /**
         * Looked for until a row the search had to run was one the runs had none left for.
         *
         * <p>Only where a run was refused. A row run already costs nothing to look at again, so a
         * search made with no runs left can still answer from rows run before, and one that did is
         * {@link Searched} or a row that goes on — never this.
         *
         * @param came   what the search had come to when it stopped
         * @param figure what ran out
         */
        record CutShort(CameToNothing came, CompositionBudget figure) implements WayPast {}

        /** Not looked for, because nothing here can hold a row to it. */
        record NotSearchable(Barrier why) implements WayPast {}
    }

    /** Why a way past a guard is one no search can be made for. */
    public enum Barrier {

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
