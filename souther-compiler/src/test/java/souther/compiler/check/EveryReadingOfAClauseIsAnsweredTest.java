package souther.compiler.check;

import souther.compiler.diag.SourcePos;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a clause owes and what came of reading it are held apart, and every answer that can be
 * written down is one somebody wrote.
 *
 * <p>These are about the values rather than about a program, because what they hold is that certain
 * answers cannot be written down. A program cannot demonstrate the absence of a state; the
 * constructors are what keep it absent, and this is what holds them to it. What a given clause comes
 * to is asked of programs instead ({@code InvariantCapabilitiesTest}).
 */
class EveryReadingOfAClauseIsAnsweredTest {

    private static final SourcePos AT = new SourcePos(3, 5);

    private static final FragmentReason WHY = new FragmentReason.ItsShapeIsNotRead();

    /**
     * A reading that ran to the end has a part to point at.
     *
     * <p>An empty answer is what a reading that never ran would produce as well, so a clause with
     * nothing to establish has to be one somebody wrote down — {@link CapabilityResult.Decided} —
     * rather than the absence of one. Read off an emptiness, {@code invariant 1 >= 0} came back as a
     * clause the static checker cannot represent and no guard discharges.
     */
    @Test
    void aReadingThatFinishedHasAPartToPointAt() {
        assertThrows(IllegalArgumentException.class, () -> new CapabilityResult.Analyzed(List.of()));
    }

    /** And a part the check carried has somewhere to have carried it, for the same reason one step
     *  down: a part with no route is the other arm, said with what stopped the reading. */
    @Test
    void aPartTheCheckCarriedHasARoute() {
        assertThrows(IllegalArgumentException.class, () -> new RequiredPart.Routed(Set.of()));
    }

    /**
     * The parts of a clause are everything it takes, and the routes of a part are alternatives.
     *
     * <p>Which is the whole reason they are two levels. A clause read as a bound in one part and as
     * a term in another is discharged by neither guard alone; flattened together, an author reading
     * "derivable" writes the guard that implies the bound and finds the construction still refused.
     * The alternatives belong inside a part, which is where the check treats them as alternatives
     * ({@link Predicates.Clause#dischargedBy}).
     */
    @Test
    void everyPartIsOwedAndTheRoutesOfOneArePicked() {
        CapabilityResult.Analyzed two = CapabilityResult.Analyzed.of(
                new RequiredPart.Routed(Set.of(new StaticRoute.AsABound())),
                new RequiredPart.Routed(Set.of(new StaticRoute.AsATerm())));
        CapabilityResult.Analyzed one = CapabilityResult.Analyzed.routed(
                new StaticRoute.AsABound(), new StaticRoute.AsATerm());

        assertEquals(2, two.parts().size(), "two things to establish, not two ways to establish one");
        assertEquals(1, one.parts().size());
        assertTrue(one.parts().get(0) instanceof RequiredPart.Routed it && it.routes().size() == 2,
                "one thing to establish, two ways to establish it");
    }

    /** What was not read is a part like any other, so it is said even where something else was
     *  carried: a clause is discharged only where every part of it is. */
    @Test
    void whatWasNotReadIsAPartBesideWhatWas() {
        CapabilityResult.Analyzed both = CapabilityResult.Analyzed.of(
                new RequiredPart.Routed(Set.of(new StaticRoute.AsABound())),
                new RequiredPart.OutsideTheFragment(WHY));

        assertEquals(2, both.parts().size());
        assertEquals(new RequiredPart.OutsideTheFragment(WHY), both.parts().get(1));
    }

    /**
     * A reason comes from the part the reading stopped on, and there is no arm for a reading that
     * did not begin.
     *
     * <p>Worked out by asking the clause a second time, a walk can come back having read all of it
     * while the first one gave up, and the answer then has to be some word for the two disagreeing.
     * There was one, and this is the check that nobody adds it back.
     */
    @Test
    void aReasonIsWhatTheReadingStoppedOnAndNothingElse() {
        assertEquals(Set.of("ItCallsAnOperation", "ItsShapeIsNotRead"),
                Set.of(FragmentReason.class.getPermittedSubclasses()).stream()
                        .map(Class::getSimpleName).collect(java.util.stream.Collectors.toSet()));
    }

    /** The obligation is the clause's and does not move when a reading does, so the name a clause was
     *  declared with is put on the obligation and what was read of it is left alone. */
    @Test
    void namingAClauseLeavesWhatWasReadOfItAlone() {
        ClauseDischarge read = new ClauseDischarge(new DischargeObligation(AT),
                CapabilityResult.Analyzed.routed(new StaticRoute.AsABound()));

        ClauseDischarge named = read.named(Optional.of("nonNegative"));

        assertEquals(Optional.of("nonNegative"), named.owed().name());
        assertEquals(AT, named.owed().clause());
        assertEquals(read.capability(), named.capability());
    }

    /** A clause always owes establishment, so there is no way to hold one with nothing owed. */
    @Test
    void aClauseAlwaysOwesEstablishment() {
        assertThrows(IllegalArgumentException.class, () -> new ClauseDischarge(null,
                CapabilityResult.Analyzed.routed(new StaticRoute.AsABound())));
    }

    /**
     * Both conjuncts decide a clause together, and either failing decides it.
     *
     * <p>{@code a && b} holds where both hold and fails where either fails; where one folds and the
     * other does not, the clause is not decided and what the other owes is what there is to
     * establish. Taken from one conjunct, {@code 1 >= 0 && value >= 0} would have come back as a
     * clause that holds of every value, with the bound nobody was told about.
     *
     * <p>No program reaches this. A conjunction an author writes is split into conjuncts before the
     * clause is read, and one a helper brings arrives as the call, which is read as a term — so the
     * two halves are never folded together today. It is here because the walk composes this way and
     * the composing is what would be wrong.
     */
    @Test
    void aConjunctionIsDecidedOnlyAsBothOfItsHalvesAre() {
        assertEquals(Predicates.Fold.HOLDS, Predicates.Fold.HOLDS.and(Predicates.Fold.HOLDS));
        assertEquals(Predicates.Fold.FAILS, Predicates.Fold.HOLDS.and(Predicates.Fold.FAILS));
        assertEquals(Predicates.Fold.FAILS, Predicates.Fold.FAILS.and(Predicates.Fold.NOT_DECIDED));
        assertEquals(Predicates.Fold.NOT_DECIDED,
                Predicates.Fold.HOLDS.and(Predicates.Fold.NOT_DECIDED));
    }
}
