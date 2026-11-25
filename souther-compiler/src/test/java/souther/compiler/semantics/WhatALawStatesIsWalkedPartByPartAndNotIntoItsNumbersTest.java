package souther.compiler.semantics;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The statements a law makes, walked from the law through the parts of a conjunction or a
 * disjunction and what some element is said to meet, the law first and each part in turn.
 *
 * <p>Not into a number it compares: a count of the elements meeting something holds a statement of
 * its own, which a reader asking about the numbers goes into on purpose.
 */
class WhatALawStatesIsWalkedPartByPartAndNotIntoItsNumbersTest {

    private static final LawProposition<String> FIRST =
            new LawProposition.Same<>(new LawSubject.ElementOf<>("a"), new LawSubject.ElementOf<>("b"),
                    true);
    private static final LawProposition<String> SECOND =
            new LawProposition.Same<>(new LawSubject.ElementOf<>("c"), new LawSubject.ElementOf<>("d"),
                    true);

    @Test
    void theLawIsVisitedFirstAndThenEachPartInTurnAtEveryDepth() {
        LawProposition<String> law = new LawProposition.Any<>(List.of(
                new LawProposition.All<>(List.of(new LawProposition.Always<>(true), FIRST)),
                new LawProposition.SomeElement<>("xs", SECOND, true)));
        List<LawProposition<String>> visited = new ArrayList<>();
        law.firstStated(each -> {
            visited.add(each);
            return null;
        });
        assertEquals(6, visited.size());
        assertEquals(law, visited.getFirst());
        assertEquals(FIRST, visited.get(3));
        assertEquals(SECOND, visited.get(5));
        assertEquals(FIRST, law.firstStated(
                each -> each instanceof LawProposition.Same<String> ? each : null));
        assertTrue(law.anyStated(each -> each.equals(SECOND)));
    }

    @Test
    void aStatementInsideANumberIsNotOneTheLawMakes() {
        LawProposition<String> law = new LawProposition.Compared<>(
                LinearForm.atom(new LawNumber.HowManyMeet<>("xs", FIRST)), Rel.GE);
        assertFalse(law.anyStated(each -> each instanceof LawProposition.Same<String>));
    }
}
