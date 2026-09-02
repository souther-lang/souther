package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.values.UnreadReason;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every way a rule of a value goes ungathered, and what a position stopped only by it comes to.
 *
 * <p>The seal refuses a way nobody answered for: {@link FieldDomains#whyNothingReached} switches
 * over {@link RulesMissed} with no {@code default}, so an eighth is a build failure. What it does
 * not refuse is a way moved from one answer to the other, and that is what this holds.
 *
 * <p><b>Which is the mistake this pair of types was made to stop.</b> These seven were a
 * {@code Set<RuleKey>} and one {@code UnreadReason}, and one of them — a walk that went as far as
 * the fields it could afford to seed — is a figure this compiler compared a depth against while the
 * other six are not. A run allowed to read further goes past the first and meets the other six
 * again, so a reader of a measure asking whether to measure again with more was answered the same
 * either way.
 *
 * <p>So the coarsening is written out here rather than arrived at. The rows are what someone
 * changing an answer has to edit, and what this asks is not whether the code is right but whether
 * the person moving a row meant to move it.
 */
class WhatEachWayOfMissingARuleComesToIsWrittenDownOnceTest {

    /**
     * Every way a rule goes ungathered, and what it comes to alone.
     *
     * <p>Written as {@code borne/reason}: what a construction can no longer be refused by, and the
     * reason a position stopped only in this way comes to. What that reason then says about a wider
     * run is written where the reasons are ({@code WhatEachWayOfDrawingNoLineLeavesIsWrittenDownOnce}),
     * so neither table restates the other's answer.
     */
    private static Map<String, String> theWaysARuleIsMissed() {
        Map<String, String> table = new LinkedHashMap<>();
        // The one figure among them. `GuaranteeWalk.FIELDS_SEEDED` is what a walk over a body can
        // afford to read, and its own comment calls it a cost bound rather than a rule of the
        // model — so a run that affords more need not stop at this position at all.
        table.put("WalkStopped[PAST_THE_DEPTH]",
                "BY_EVERY_VALUE/NOT_REACHED_PAST_DEPTH_LIMIT");
        // A name the reader is supposing holds values. Nothing was compared against anything: the
        // reading was asked a question that stops there, and it stops there however much is
        // allowed.
        table.put("WalkStopped[ASKED_TO_STOP]", "BY_EVERY_VALUE/NOT_REACHED");
        // A type met already on the way down, which is a fact about the type graph. Its `Borne` is
        // the one that differs, and it is `PathEngine.leftBy`'s answer rather than this table's.
        table.put("WalkStopped[ALREADY_ENTERED]", "BY_SOME_VALUES/NOT_REACHED");
        table.put("ClauseNotTyped", "BY_EVERY_VALUE/NOT_REACHED");
        table.put("ClauseLost", "BY_EVERY_VALUE/NOT_REACHED");
        table.put("PositionNotOpened", "BY_EVERY_VALUE/NOT_REACHED");
        table.put("ClauseNotAsked", "BY_EVERY_VALUE/NOT_REACHED");
        table.put("NoReadingWasMade", "BY_EVERY_VALUE/NOT_REACHED");
        table.put("ReadingFellOver", "BY_EVERY_VALUE/NOT_REACHED");
        return table;
    }

    /** The table, held against what the ways themselves answer. */
    @Test
    void everyWayOfMissingARuleSaysWhatItComesTo() {
        Map<String, String> said = new LinkedHashMap<>();
        for (RulesMissed each : everyWay()) {
            said.put(nameOf(each),
                    each.borne() + "/" + FieldDomains.whyNothingReached(Set.of(each)));
        }

        assertEquals(theWaysARuleIsMissed(), said);
    }

    /**
     * A position more than one way reaches is short after the depth is raised, so it says so.
     *
     * <p>The property the rows cannot state for themselves, and the one a fold gets wrong. Read as
     * "any of them was the depth", a position a depth and an untyped clause both reach would send a
     * person to measure the same thing again with more — and the clause would still be untyped.
     */
    @Test
    void aDepthBesideAnythingElseIsNotADepthTheRunCanGetPast() {
        RulesMissed depth = new RulesMissed.WalkStopped(GuaranteeWalk.Stop.PAST_THE_DEPTH);

        assertEquals(UnreadReason.NOT_REACHED_PAST_DEPTH_LIMIT,
                FieldDomains.whyNothingReached(Set.of(depth)));
        for (RulesMissed other : everyWay()) {
            if (other.equals(depth)) {
                continue;
            }
            Set<RulesMissed> both = new LinkedHashSet<>(List.of(depth, other));
            assertEquals(UnreadReason.NOT_REACHED, FieldDomains.whyNothingReached(both),
                    () -> "a position " + other + " also reaches stays short past the depth");
        }
    }

    /**
     * Every member of the seal has a row, read from the seal rather than from the list below.
     *
     * <p>The list is written out because a way with an argument cannot be made from its class
     * alone. That it holds every one of them is not the list's word: this is, and an eighth way
     * added and left out of it comes back here with nothing to say about it.
     */
    @Test
    void everyWayThereIsHasARowAbove() {
        Set<String> written = new LinkedHashSet<>();
        for (Class<?> each : RulesMissed.class.getPermittedSubclasses()) {
            written.add(each.getSimpleName());
        }
        Set<String> listed = new LinkedHashSet<>();
        for (RulesMissed each : everyWay()) {
            listed.add(each.getClass().getSimpleName());
        }

        assertEquals(written, listed, "a way of missing a rule that no row above answers for");
    }

    /**
     * One of each, with every value of the walk's own stop.
     *
     * <p>The walk's three are here as three rows rather than one, because which of them it was is
     * exactly what the coarsening is about: one is a figure and two are not, and a row per arm
     * would have said one thing about all three.
     */
    private static List<RulesMissed> everyWay() {
        List<RulesMissed> out = new java.util.ArrayList<>();
        for (GuaranteeWalk.Stop stop : GuaranteeWalk.Stop.values()) {
            out.add(new RulesMissed.WalkStopped(stop));
        }
        out.add(new RulesMissed.ClauseNotTyped());
        out.add(new RulesMissed.ClauseLost());
        out.add(new RulesMissed.PositionNotOpened());
        out.add(new RulesMissed.ClauseNotAsked());
        out.add(new RulesMissed.NoReadingWasMade());
        out.add(new RulesMissed.ReadingFellOver());
        return out;
    }

    /** What the reason is called in the rows: the walk's own three are told apart by their stop. */
    private static String nameOf(RulesMissed why) {
        return why instanceof RulesMissed.WalkStopped(GuaranteeWalk.Stop stop)
                ? "WalkStopped[" + stop + "]" : why.getClass().getSimpleName();
    }
}
