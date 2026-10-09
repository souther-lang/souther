package souther.compiler.partition;

import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.StatedComparison;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * What each condition met over one reading of the input states, read once however many readers
 * ask.
 *
 * <p>A comparison a fork tests is asked what it states three times over: for what a row coming out
 * each way of the fork has done, and for the line it draws. Those are one statement, read under
 * the same names, so it is read once and each reader takes it from here. A truth a fork tests is
 * asked once for each way, and is the same.
 *
 * <p>Keyed on the nodes and not on what they are equal to. A comparison is the node it is written
 * as, and two nodes alike in every part are two comparisons in two places that may be read under
 * different names; the names are the other half of the key. A comparison this compiler composes
 * where it is asked, such as an emptiness check read as a size against nought, is a new node each
 * time and is read each time.
 *
 * <p>Of one reading of the input, which is held and asked for: a statement is read against the
 * input's declarations as well as its names, and an answer under one reading is no answer under
 * another. And one for that reading, kept with it ({@link InputReading#derived}): the readers of
 * one input — the lines drawn, the ways to them, the decisions, the guards — ask about the same
 * conditions, and one kept by each of them would read every condition once per reader.
 *
 * <p>The arms of a fork that chooses by no condition are kept here too, every arm of a fork at
 * once ({@link Pullback#ofTheArms}): what one arm states is a fact of the whole fork, so it is
 * read once for the fork and not once for each arm a reader asks about.
 */
final class WhatConditionsState {

    private final InputReading read;
    private final Map<AComparison, Pullback.OnTheInput> comparisons = new HashMap<>();
    private final Map<ANode, Pullback.Pulled> truths = new HashMap<>();
    private final Map<ANode, List<Pullback.Pulled>> arms = new HashMap<>();

    private WhatConditionsState(InputReading read) {
        this.read = read;
    }

    /** What the conditions met over {@code read} state, kept for that reading. */
    static WhatConditionsState of(InputReading read) {
        return read.derived(WhatConditionsState.class, WhatConditionsState::new);
    }

    /** A comparison, by the nodes its sides are and what its operator placed, under names. */
    private record AComparison(Core left, Core right, ComparisonClaim claim, InputReads reads) {

        @Override
        public boolean equals(Object other) {
            return other instanceof AComparison that && left == that.left && right == that.right
                    && claim.equals(that.claim) && reads.equals(that.reads);
        }

        @Override
        public int hashCode() {
            int hash = System.identityHashCode(left);
            hash = hash * 31 + System.identityHashCode(right);
            hash = hash * 31 + claim.hashCode();
            return hash * 31 + reads.hashCode();
        }
    }

    /** A truth, or a fork whose arms are entered, by the node it is, under names. */
    private record ANode(Core value, InputReads reads) {

        @Override
        public boolean equals(Object other) {
            return other instanceof ANode that && value == that.value && reads.equals(that.reads);
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(value) * 31 + reads.hashCode();
        }
    }

    /** What {@code comparison} states with its names as {@code reads} has them, under
     *  {@code read}. */
    Pullback.OnTheInput comparison(StatedComparison comparison, InputReads reads,
                                   InputReading read) {
        heldTo(read);
        return comparisons.computeIfAbsent(
                new AComparison(comparison.left(), comparison.right(), comparison.claim(), reads),
                _ -> Pullback.ofAComparisonOnTheInput(comparison, reads, read));
    }

    /** What {@code truth} holding states with its names as {@code reads} has them, under
     *  {@code read}. */
    Pullback.Pulled truth(Core truth, InputReads reads, InputReading read) {
        heldTo(read);
        return truths.computeIfAbsent(new ANode(truth, reads),
                _ -> Pullback.ofATruth(truth, reads, read, Optional.empty()));
    }

    /** What a run entering arm {@code part} of {@code fork} states with its names as {@code reads}
     *  has them ({@link Pullback#ofTheArms}). */
    Pullback.Pulled arm(Core fork, int part, InputReads reads) {
        return arms.computeIfAbsent(new ANode(fork, reads),
                _ -> Pullback.ofTheArms(fork, reads, read, Optional.empty())).get(part);
    }

    private void heldTo(InputReading asked) {
        if (asked != read) {
            throw new IllegalArgumentException(
                    "what a condition states is kept for one reading of the input, and was asked"
                            + " under another");
        }
    }
}
