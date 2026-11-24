package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;

import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a case is refuted under some truths settled, asked of the case that keeps what it
 * answered ({@link TheCaseALineDecidesIn#noTruthMakesItHoldUnder}), is what trying every truth of
 * the questions left open comes to, the first time it is asked and every time after.
 *
 * <p>Every way four questions are settled, held, failing or open, is asked twice of one case, from
 * arrays the caller changes between the asks, and once of another case.
 */
class WhatACaseRefutesUnderSomeTruthsIsAskedOnceTest {

    private static final int QUESTIONS = 4;
    private static final DecisionSubject[] SUBJECTS = new DecisionSubject[QUESTIONS];

    static {
        for (int at = 0; at < QUESTIONS; at++) {
            SUBJECTS[at] = new DecisionSubject.AnInput(TermPath.of("q" + at));
        }
    }

    @Test
    void whatWasAnsweredIsAnsweredAgainForTheSameTruthsWhateverTheArrayIsLaterMadeInto() {
        Proposition decides = decides();
        TheCaseALineDecidesIn kept = new TheCaseALineDecidesIn(decides);
        TheCaseALineDecidesIn other = new TheCaseALineDecidesIn(decides);
        int refuted = 0;
        int notRefuted = 0;
        for (int way = 0; way < Math.pow(3, QUESTIONS); way++) {
            Boolean[] truths = settled(way);
            Boolean[] before = truths.clone();
            boolean expected = noTruthMakesItHold(decides, before);

            assertEquals(expected, kept.noTruthMakesItHoldUnder(truths), () -> describe(before));
            assertArrayEquals(before, truths, "the truths are as they were");

            // The array that was asked is changed; what is asked next is the same truths.
            for (int at = 0; at < QUESTIONS; at++) {
                truths[at] = truths[at] == null ? Boolean.TRUE : null;
            }
            assertEquals(expected, kept.noTruthMakesItHoldUnder(before.clone()),
                    () -> "again " + describe(before));
            assertEquals(expected, other.noTruthMakesItHoldUnder(before.clone()),
                    () -> "another case " + describe(before));
            if (expected) {
                refuted++;
            } else {
                notRefuted++;
            }
        }
        int some = refuted;
        int others = notRefuted;
        assertTrue(some > 0 && others > 0, () -> "refuted " + some + ", not refuted " + others);
    }

    @Test
    void truthsThatDifferOnlyInWhetherAQuestionIsOpenAreTwoQuestions() {
        TheCaseALineDecidesIn kept = new TheCaseALineDecidesIn(decides());
        // Every question open leaves the case a truth that holds it; q0 and q1 failing with q2
        // and q3 holding leaves none.
        assertEquals(false, kept.noTruthMakesItHoldUnder(
                new Boolean[] {null, null, null, null}));
        assertEquals(true, kept.noTruthMakesItHoldUnder(
                new Boolean[] {false, false, true, true}));
        assertEquals(false, kept.noTruthMakesItHoldUnder(
                new Boolean[] {null, null, null, null}));
    }

    /** (q0 or q1) and (not q1 or q2) and (not q0 or q3) and (not q2 or not q3). */
    private static Proposition decides() {
        return new Proposition.All(List.of(
                new Proposition.Any(List.of(truth(0, true), truth(1, true))),
                new Proposition.Any(List.of(truth(1, false), truth(2, true))),
                new Proposition.Any(List.of(truth(0, false), truth(3, true))),
                new Proposition.Any(List.of(truth(2, false), truth(3, false)))));
    }

    private static Proposition truth(int question, boolean holds) {
        return new Proposition.Truth(SUBJECTS[question], holds);
    }

    /** The {@code way}th of the ways to settle the questions, each held, failing or open. */
    private static Boolean[] settled(int way) {
        Boolean[] truths = new Boolean[QUESTIONS];
        int left = way;
        for (int at = 0; at < QUESTIONS; at++) {
            int pick = left % 3;
            left /= 3;
            truths[at] = pick == 0 ? Boolean.TRUE : pick == 1 ? Boolean.FALSE : null;
        }
        return truths;
    }

    private static boolean noTruthMakesItHold(Proposition decides, Boolean[] settled) {
        for (int chosen = 0; chosen < 1 << QUESTIONS; chosen++) {
            Boolean[] truths = settled.clone();
            for (int at = 0; at < QUESTIONS; at++) {
                if (truths[at] == null) {
                    truths[at] = (chosen & 1 << at) != 0;
                }
            }
            if (holds(decides, truths)) {
                return false;
            }
        }
        return true;
    }

    private static boolean holds(Proposition stated, Boolean[] truths) {
        return switch (stated) {
            case Proposition.All all -> all.parts().stream().allMatch(part -> holds(part, truths));
            case Proposition.Any any -> any.parts().stream().anyMatch(part -> holds(part, truths));
            case Proposition.Truth truth -> truths[indexOf(truth.of())] == truth.holds();
            default -> throw new IllegalStateException(stated.toString());
        };
    }

    private static int indexOf(DecisionSubject subject) {
        for (int at = 0; at < QUESTIONS; at++) {
            if (SUBJECTS[at].equals(subject)) {
                return at;
            }
        }
        throw new IllegalStateException(subject.toString());
    }

    private static String describe(Boolean[] truths) {
        return Arrays.toString(truths);
    }
}
