package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.partition.CompositionBudget;

import java.math.BigInteger;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * No case is held nowhere ({@link DecidingCase.Cases#NONE}): an alternative that is no case adds
 * nothing and is left out, and cases held together with no case are none — so every reader of
 * the cases, counting them, naming what stopped them or asking each, comes to what it comes to
 * without it.
 */
class NoCaseIsHeldNowhereTest {

    private static Proposition truth(String at) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(at)), true);
    }

    private static DecidingCase.Cases one(String at) {
        return new DecidingCase.Cases.One(truth(at));
    }

    private static final DecidingCase.Cases.NotTakenApart STOPPED =
            new DecidingCase.Cases.NotTakenApart(CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN);

    /** Two choices held together, beside cases nobody took apart: four ways and one more. */
    private static final DecidingCase.Cases SOME = new DecidingCase.Cases.EachOf(List.of(
            DecidingCase.Cases.together(List.of(
                    new DecidingCase.Cases.EachOf(List.of(one("a"), one("b"))),
                    new DecidingCase.Cases.EachOf(List.of(one("c"), one("d"))))),
            one("e")));

    private static final Proposition SAID = truth("said");

    @Test
    void anAlternativeThatIsNoCaseAddsNoWay() {
        DecidingCase.Cases beside = new DecidingCase.Cases.EachOf(List.of(SOME,
                DecidingCase.Cases.NONE));
        assertEquals(SOME.waysOfChoosing(100), beside.waysOfChoosing(100));
        assertEquals(SOME.structuralWays(CaseCount.WAYS_A_COUNT_IS_HELD_TO),
                beside.structuralWays(CaseCount.WAYS_A_COUNT_IS_HELD_TO));
        assertEquals(List.of(SOME), ((DecidingCase.Cases.EachOf) beside).alternatives(),
                "left out where the choice is made");
    }

    @Test
    void casesHeldTogetherWithNoCaseAreNone() {
        DecidingCase.Cases with = DecidingCase.Cases.together(List.of(SOME, STOPPED,
                DecidingCase.Cases.NONE));
        assertSame(DecidingCase.Cases.NONE, with);
        assertEquals(0, with.waysOfChoosing(100));
        assertEquals(BigInteger.ZERO, with.structuralWays(CaseCount.WAYS_A_COUNT_IS_HELD_TO));
        assertEquals(Set.of(), with.notTakenApartAt(),
                "what stopped cases held beside no case stopped no case");
    }

    /** Asked of each case, what is beside no case is asked nowhere: the same cases are shown to
     *  divide rows, and the same figures stop the rest. */
    @Test
    void askingTheCasesFindsWhatItFindsWithoutNoCase() {
        DecidingCase.Cases withStopped = new DecidingCase.Cases.EachOf(List.of(SOME, STOPPED));
        DecidingCase.Cases beside = new DecidingCase.Cases.EachOf(List.of(withStopped,
                DecidingCase.Cases.together(List.of(one("f"), STOPPED,
                        DecidingCase.Cases.NONE))));
        CasesOfALineAsked.Found without = CasesOfALineAsked.casesOf(
                new DecidingCase(SAID, withStopped),
                condition -> CasesOfALineAsked.Crossing.MAY_CROSS);
        CasesOfALineAsked.Found with = CasesOfALineAsked.casesOf(new DecidingCase(SAID, beside),
                condition -> CasesOfALineAsked.Crossing.MAY_CROSS);
        assertEquals(without.decidesIn(), with.decidesIn());
        assertEquals(without.notWorkedOut(), with.notWorkedOut());
        DecidingCase.Cases inOrder = CasesOfALineAsked.heldFirst(withStopped);
        DecidingCase.Cases besideInOrder = CasesOfALineAsked.heldFirst(beside);
        assertEquals(inOrder.waysOfChoosing(100), besideInOrder.waysOfChoosing(100));
        assertEquals(inOrder.notTakenApartAt(), besideInOrder.notTakenApartAt());
    }
}
