package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.semantics.ConditionJoin;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A step that stopped for anything besides coming to too many parts is told so, whatever the step
 * above it came to.
 *
 * <p>A step that comes to too many parts is given up as one part nothing read, and what stopped
 * inside it is not in what it is given up as. A stop that depends on the reading, such as the
 * readings having run out, hidden there would let the reading be taken again where it would not
 * come out the same, so the question is asked of the steps and not of what they state.
 */
class AStepThatStoppedForAnythingBesidesItsSizeIsToldSoWhateverItCameToTest {

    /** Levels that come to more parts than a step is concluded with, each holding the one before
     *  twice. */
    private static final int PAST_THE_SIZE = 16;

    private static Derivation leaf(String name) {
        return new Derivation.ATruthOfASubject(new DecisionSubject.AnInput(TermPath.of(name)),
                true);
    }

    private static Derivation stopped(WhyUnread why) {
        return new Derivation.Stopped(why, false);
    }

    /** {@code base}, put through {@code levels} of {@code prev && (x || prev)}. */
    private static Derivation chain(Derivation base, int levels) {
        Derivation each = base;
        for (int level = 1; level <= levels; level++) {
            each = new Derivation.Joined(ConditionJoin.BOTH, each,
                    new Derivation.Joined(ConditionJoin.EITHER, leaf("x" + level), each));
        }
        return each;
    }

    @Test
    void aStepThatStoppedForNothingIsToldSo() {
        Conclusion trying = Conclusion.reusing();
        Derivation step = chain(leaf("a"), 3);
        assertNull(Proposition.firstStopIn(trying.of(step)));
        assertFalse(trying.stoppedBesidesItsSize(step));
    }

    @Test
    void aStepThatCameToTooManyPartsAndStoppedForNothingElseIsToldSo() {
        Conclusion trying = Conclusion.reusing();
        Derivation step = chain(leaf("a"), PAST_THE_SIZE);
        assertInstanceOf(WhyUnread.MorePartsThanAreConcluded.class,
                Proposition.firstStopIn(trying.of(step)));
        assertFalse(trying.stoppedBesidesItsSize(step));
    }

    @Test
    void aStepThatStoppedAtTheSizeItselfIsToldSo() {
        Conclusion trying = Conclusion.reusing();
        Derivation step = chain(stopped(WhyUnread.PAST_THE_PARTS), 3);
        assertTrue(Proposition.firstStopIn(trying.of(step)) != null);
        assertFalse(trying.stoppedBesidesItsSize(step));
    }

    @Test
    void aStepThatStoppedForSomethingElseIsToldSo() {
        Conclusion trying = Conclusion.reusing();
        Derivation step = chain(stopped(WhyUnread.PAST_THE_TOTAL_READINGS), 3);
        assertInstanceOf(WhyUnread.MoreTotalReadingsThanAreMade.class,
                Proposition.firstStopIn(trying.of(step)));
        assertTrue(trying.stoppedBesidesItsSize(step));
    }

    /**
     * What it states says it came to too many parts and nothing else, which is what a reader
     * that asks of what it states takes it to have stopped for.
     */
    @Test
    void aStopHiddenBySizeIsToldSoAllTheSame() {
        Conclusion trying = Conclusion.reusing();
        Derivation step = chain(stopped(WhyUnread.PAST_THE_TOTAL_READINGS), PAST_THE_SIZE);
        Proposition stated = trying.of(step);
        assertInstanceOf(WhyUnread.MorePartsThanAreConcluded.class,
                Proposition.firstStopIn(stated));
        assertTrue(Proposition.stopsOnlyPastThePartsReading().read(stated),
                "nothing in what it states says more");
        assertTrue(trying.stoppedBesidesItsSize(step));
    }

    /** A step concluded already, found again under another, is told as it was. */
    @Test
    void aStepFoundAgainUnderAnotherIsToldAsItWas() {
        Conclusion trying = Conclusion.reusing();
        Derivation hidden = chain(stopped(WhyUnread.PAST_THE_TOTAL_READINGS), PAST_THE_SIZE);
        trying.of(hidden);
        Derivation above = new Derivation.Joined(ConditionJoin.BOTH, hidden, leaf("z"));
        trying.of(above);
        assertTrue(trying.stoppedBesidesItsSize(above));
        Derivation clear = chain(leaf("a"), PAST_THE_SIZE);
        trying.of(clear);
        Derivation clearAbove = new Derivation.Joined(ConditionJoin.BOTH, clear, leaf("z"));
        trying.of(clearAbove);
        assertFalse(trying.stoppedBesidesItsSize(clearAbove));
    }

    @Test
    void aStepNeverConcludedHereIsToldAsHavingStopped() {
        assertTrue(Conclusion.reusing().stoppedBesidesItsSize(leaf("a")));
    }
}
