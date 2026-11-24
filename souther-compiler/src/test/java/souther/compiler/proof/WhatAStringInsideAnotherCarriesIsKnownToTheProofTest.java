package souther.compiler.proof;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.StringContainment;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a string standing inside another says of the two, and what its not standing says, are told
 * to a proof apart: standing inside, the one inside holds no more code points than the one around
 * it; not standing inside, the one inside holds some, because the empty string stands inside every
 * string, in each place a string can stand.
 *
 * <p>Each is a condition of its own side and not of the other: a string no longer than another need
 * not stand inside it, and a string holding some code points may stand inside another.
 */
class WhatAStringInsideAnotherCarriesIsKnownToTheProofTest {

    private static final Value INNER = new Value.Argument(0);
    private static final Value OUTER = new Value.Argument(1);

    private static LawProposition<Value> inside(StringContainment where, boolean holds) {
        return new LawProposition.Inside<>(new LawSubject.Argument<>(INNER),
                new LawSubject.Argument<>(OUTER), where, holds);
    }

    private static LinearForm<LawNumber<Value>> size(Value of) {
        return LinearForm.atom(new LawNumber.SizeOf<>(new LawSubject.Argument<>(of)));
    }

    private static LawProposition<Value> innerNoLongerThanOuter() {
        return Props.compared(size(INNER), Rel.LE, size(OUTER));
    }

    private static LawProposition<Value> innerHoldsSome() {
        return Props.compared(size(INNER), Rel.GE, Props.constant(1));
    }

    private static boolean follows(LawProposition<Value> given, LawProposition<Value> goal) {
        return Validity.follows(List.of(given), goal, _ -> Granularity.DISCRETE);
    }

    @Test
    void whereAStringStandsInsideItIsNoLongerThanTheOneAroundIt() {
        for (StringContainment where : StringContainment.values()) {
            assertTrue(follows(inside(where, true), innerNoLongerThanOuter()), where.name());
            assertFalse(follows(inside(where, true), innerHoldsSome()),
                    where.name() + ": the empty string stands inside every string");
        }
    }

    @Test
    void whereAStringDoesNotStandInsideItHoldsSomeCodePoints() {
        for (StringContainment where : StringContainment.values()) {
            assertTrue(follows(inside(where, false), innerHoldsSome()), where.name());
            assertFalse(follows(inside(where, false), innerNoLongerThanOuter()),
                    where.name() + ": a string longer than another does not stand inside it, "
                            + "and neither does a shorter one that is not part of it");
        }
    }

    @Test
    void theConditionOfOneSideIsNoLawOfTheOther() {
        assertFalse(follows(innerNoLongerThanOuter(), inside(StringContainment.ANYWHERE, true)));
        assertFalse(follows(innerHoldsSome(), inside(StringContainment.ANYWHERE, false)));
    }
}
