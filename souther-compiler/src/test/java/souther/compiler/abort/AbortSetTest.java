package souther.compiler.abort;

import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

class AbortSetTest {

    @Test
    void noneHoldsNothing() {
        assertTrue(AbortSet.NONE.isEmpty());
        for (AbortKind kind : AbortKind.values()) {
            assertFalse(AbortSet.NONE.contains(kind));
        }
    }

    @Test
    void ofHoldsExactlyWhatItWasGiven() {
        AbortSet one = AbortSet.of(AbortKind.INVARIANT_NOT_HELD);
        assertTrue(one.contains(AbortKind.INVARIANT_NOT_HELD));
        assertFalse(one.contains(AbortKind.UNREACHABLE_REACHED));
        assertFalse(one.isEmpty());
    }

    @Test
    void ofHoldsMoreThanOneReasonForOneSite() {
        AbortSet both = AbortSet.of(AbortKind.DIVISION_BY_ZERO, AbortKind.ANSWER_HAS_NO_PLACE);
        assertTrue(both.contains(AbortKind.DIVISION_BY_ZERO));
        assertTrue(both.contains(AbortKind.ANSWER_HAS_NO_PLACE));
        assertEquals(Set.of(AbortKind.DIVISION_BY_ZERO, AbortKind.ANSWER_HAS_NO_PLACE), both.kinds());
    }

    @Test
    void copyOfAnEmptySetIsTheSameInstanceAsNone() {
        assertSame(AbortSet.NONE, AbortSet.copyOf(Set.of()));
    }

    @Test
    void unionKeepsEveryReasonEitherSideAnswers() {
        AbortSet left = AbortSet.of(AbortKind.DIVISION_BY_ZERO);
        AbortSet right = AbortSet.of(AbortKind.ANSWER_HAS_NO_PLACE, AbortKind.INVALID_BOUNDS);

        AbortSet merged = left.union(right);

        assertEquals(
                Set.of(AbortKind.DIVISION_BY_ZERO, AbortKind.ANSWER_HAS_NO_PLACE,
                        AbortKind.INVALID_BOUNDS),
                merged.kinds());
    }

    @Test
    void unionWithNoneAnswersTheOtherSideUnchanged() {
        AbortSet some = AbortSet.of(AbortKind.UNREACHABLE_REACHED);
        assertEquals(some, some.union(AbortSet.NONE));
        assertEquals(some, AbortSet.NONE.union(some));
    }

    @Test
    void equalityIsByMembershipAloneNotByHowItWasBuilt() {
        AbortSet built = AbortSet.of(AbortKind.ENSURES_NOT_HELD).union(AbortSet.NONE);
        AbortSet direct = AbortSet.of(AbortKind.ENSURES_NOT_HELD);
        assertEquals(direct, built);
        assertEquals(direct.hashCode(), built.hashCode());
    }
}
