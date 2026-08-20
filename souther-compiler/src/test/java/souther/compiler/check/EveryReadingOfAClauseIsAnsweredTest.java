package souther.compiler.check;

import souther.compiler.diag.SourcePos;

import org.junit.jupiter.api.Test;

import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
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

    private static final FragmentReason WHY = new FragmentReason.ItsShapeIsNotRead();

    /** Asked for it, and the asking is what the rule is careful about. */
    private static final java.util.function.Supplier<FragmentReason> EXPENSIVE = () -> WHY;

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
        CapabilityResult.Analyzed both = CapabilityResult.analyzed(
                Set.of(new StaticReading.AsABound()), true, EXPENSIVE);

        assertEquals(Set.of(new StaticReading.AsABound(),
                        new StaticReading.OutsideTheFragment(WHY)), both.readings());
    }

    /** And a walk that read nothing at all is said once, by what stopped it rather than by an
     *  emptiness. */
    @Test
    void aClauseNothingWasReadOfIsSaidByWhatStoppedIt() {
        assertEquals(Set.of(new StaticReading.OutsideTheFragment(WHY)),
                CapabilityResult.analyzed(Set.of(), true, EXPENSIVE).readings());
    }

    /**
     * A walk that finished owing nothing is a clause that holds.
     *
     * <p>{@code Predicates} owes nothing exactly where every part of a clause folded the way it was
     * read. Said as an emptiness instead, {@code invariant 1 >= 0} came back as a clause the static
     * checker cannot represent and no guard discharges. {@code Bool.not(1 < 0)} is the shape that
     * reaches this rather than the fold, and is held to it through a program in
     * {@code InvariantCapabilitiesTest}.
     */
    @Test
    void aWalkThatOwedNothingIsAClauseThatHolds() {
        assertEquals(Set.of(new StaticReading.Decided(true)),
                CapabilityResult.analyzed(Set.of(), false, EXPENSIVE).readings());
    }

    /** What was not read is asked for only where there is something to say, since finding out what
     *  in a clause stopped the walk costs a walk of it. */
    @Test
    void whyIsAskedOnlyWhereSomethingWasNotRead() {
        boolean[] asked = {false};
        CapabilityResult.analyzed(Set.of(new StaticReading.AsABound()), false, () -> {
            asked[0] = true;
            return WHY;
        });
        assertFalse(asked[0], "nothing was left unread, so there is nothing to explain");

        CapabilityResult.analyzed(Set.of(new StaticReading.AsABound()), true, () -> {
            asked[0] = true;
            return WHY;
        });
        assertTrue(asked[0], "and it is asked where there is");
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
