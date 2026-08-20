package souther.compiler.check;

import souther.compiler.diag.SourcePos;

import org.junit.jupiter.api.Test;

import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a clause owes and what came of reading it are held apart, and a reading that finished always
 * says something.
 *
 * <p>These are about the values rather than about a program, because what they hold is that certain
 * answers cannot be written down. A program cannot demonstrate the absence of a state; the
 * constructor is what keeps it absent, and this is what holds the constructor to it. What each
 * answer comes to for a given clause is asked of programs instead
 * ({@code InvariantCapabilitiesTest}).
 */
class EveryReadingOfAClauseIsAnsweredTest {

    private static final SourcePos AT = new SourcePos(3, 5);

    /**
     * A reading that ran to the end has an answer.
     *
     * <p>This is the one that decides a program. An empty answer is what a reading that never ran
     * would produce as well, so a clause the reading owed nothing for came out as a clause nothing
     * could be made of — and {@code invariant 1 >= 0}, which holds of every value, was reported to an
     * author as one the static checker cannot represent and no guard discharges.
     */
    @Test
    void aReadingThatFinishedSaysWhatItMadeOfTheClause() {
        assertThrows(IllegalArgumentException.class,
                () -> new CapabilityResult.Analyzed(Set.of()));
    }

    /**
     * A clause read more than one way is answered more than one way.
     *
     * <p>What is written as one thing need not be read as one thing: a clause naming a helper is one
     * thing to its author and is whatever that helper states to the check, and its parts can be read
     * differently. Answered with one of the readings, an author is told what discharges half of their
     * clause and left to find out about the other half from a construction that is still refused.
     *
     * <p>Held here rather than through a program, because no program takes this shape today — a
     * clause that names a helper is read as one term and states one thing to the check. It is the day
     * the check reads further into what a clause names that a clause states two of these at once.
     */
    @Test
    void aClauseReadAsABoundAndAsATermIsAnsweredAsBoth() {
        CapabilityResult.Analyzed both = CapabilityResult.Analyzed.of(
                new StaticReading.AsABound(), new StaticReading.AsATerm());

        assertTrue(both.readings().contains(new StaticReading.AsABound()));
        assertTrue(both.readings().contains(new StaticReading.AsATerm()),
                "and the other half, which admits another guard entirely");
    }

    /**
     * What was not read is said even where something else was.
     *
     * <p>A clause part of which is outside the fragment is a clause no guard discharges, and
     * answering it by the part that was read tells an author their construction can be judged safe
     * when it cannot.
     */
    @Test
    void whatWasNotReadIsSaidBesideWhatWas() {
        CapabilityResult.Analyzed both = CapabilityResult.Analyzed.of(new StaticReading.AsABound(),
                new StaticReading.OutsideTheFragment(new FragmentReason.ItsShapeIsNotRead()));

        assertTrue(both.readings().contains(new StaticReading.AsABound()));
        assertTrue(both.readings().contains(
                new StaticReading.OutsideTheFragment(new FragmentReason.ItsShapeIsNotRead())));
    }

    /**
     * The two ways a clause can settle on its own are two answers.
     *
     * <p>They come from one fold of one expression. Kept as one — or with only the true one written
     * down — the other goes to whichever arm is nearest, which is how a clause no value satisfies
     * came to be answered as a bound any guard implying it would discharge.
     */
    @Test
    void aClauseThatHoldsAndOneThatCannotAreNotOneAnswer() {
        assertNotEquals(new StaticReading.Decided(true), new StaticReading.Decided(false));
    }

    /**
     * A reading that stopped is not a reading that concluded.
     *
     * <p>Different arms of {@link CapabilityResult}, so no reader downstream can hold one for the
     * other. Whether the clause is inside the fragment is exactly what a stopped reading did not find
     * out, and a document saying it is outside would be publishing this compiler's failure as a fact
     * about somebody's model.
     */
    @Test
    void aReadingThatStoppedIsNotOneThatConcluded() {
        CapabilityResult stopped = new CapabilityResult.AnalysisStopped("typing a clause");
        CapabilityResult concluded = CapabilityResult.Analyzed.of(
                new StaticReading.OutsideTheFragment(new FragmentReason.ItsShapeIsNotRead()));

        assertNotEquals(stopped, concluded);
    }

    /** A reason is what a reading recorded, and there is no arm for one that could not be typed:
     *  a reading that did not begin did not finish, so it has no reason of this kind to give. */
    @Test
    void aFragmentReasonIsOnlyWhatAFinishedReadingConcluded() {
        assertEquals(Set.of("ItCallsAnOperation", "ItsShapeIsNotRead",
                        "NothingAGuardCouldBeHeldAgainst"),
                Set.of(FragmentReason.class.getPermittedSubclasses()).stream()
                        .map(Class::getSimpleName).collect(java.util.stream.Collectors.toSet()));
    }

    /** The obligation is the clause's and does not move when a reading does, so the name a clause was
     *  declared with is put on the obligation and the reading is left alone. */
    @Test
    void namingAClauseLeavesWhatWasReadOfItAlone() {
        ClauseDischarge read = new ClauseDischarge(new DischargeObligation(AT),
                CapabilityResult.Analyzed.of(new StaticReading.AsABound()));

        ClauseDischarge named = read.named(Optional.of("nonNegative"));

        assertEquals(Optional.of("nonNegative"), named.owed().name());
        assertEquals(AT, named.owed().clause());
        assertEquals(read.capability(), named.capability());
    }

    /** A clause always owes establishment, so there is no way to hold one with nothing owed. */
    @Test
    void aClauseAlwaysOwesEstablishment() {
        assertThrows(IllegalArgumentException.class, () -> new ClauseDischarge(null,
                CapabilityResult.Analyzed.of(new StaticReading.AsABound())));
    }
}
