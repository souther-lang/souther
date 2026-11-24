package souther.compiler.values;

import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;
import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.WholeNumberRuns;
import souther.compiler.regex.PatternPlan;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A plan of the values a set does not hold is realized for every kind of set there is.
 *
 * <p>The plan takes any set, so what it is realized to is asked of each kind rather than of the
 * kind a caller happens to hand it today: a refusal at the last kind would be a state the type
 * admits and a later stage rejects. Each is asked to hold exactly what the set does not.
 */
class TheOtherSideOfAnyKindOfValueSetIsAValueSetTest {

    private static ValueSet otherSideOf(ValueSet set) {
        PatternPlan.Budget budget = PatternPlan.Budget.OF_ADMITTED_VALUES;
        Realizer realizer = new Realizer(budget, budget.meter(), plan -> null, (plan, made) -> { });
        return assertInstanceOf(Realization.Exact.class,
                realizer.of(AdmittedPlan.without(set))).set();
    }

    @Test
    void theOtherSideOfAFiniteSetIsEveryValueButThose() {
        ValueSet other = otherSideOf(new ValueSet.Finite(Set.of(Value.text("a"))));

        assertFalse(other.has(Value.text("a")));
        assertTrue(other.has(Value.text("b")));
    }

    @Test
    void theOtherSideOfACofiniteSetIsThoseItLeavesOut() {
        ValueSet other = otherSideOf(new ValueSet.Cofinite(Set.of(Value.text("a"))));

        assertTrue(other.has(Value.text("a")));
        assertFalse(other.has(Value.text("b")));
    }

    @Test
    void theOtherSideOfALanguageIsTheStringsItDoesNotHold() {
        PatternRead said = PatternParser.read("[a-z]+");
        ValueSet letters = ValueSet.matching(PatternPlan.of(
                assertInstanceOf(PatternRead.Read.class, said).meaning())
                .compile(PatternPlan.Budget.OF_ADMITTED_VALUES.meter()));

        ValueSet other = otherSideOf(letters);

        assertFalse(other.has(Value.text("abc")));
        assertTrue(other.has(Value.text("a1")));
        assertTrue(other.has(Value.text("")));
    }

    @Test
    void theOtherSideOfARunOfNumbersIsTheRunOfTheNumbersItLeavesOut() {
        WholeNumberRuns fiveOrMore = WholeNumberRuns.standing(Rel.GE, ExactRatio.of(5));
        ValueSet runs = ValueSet.wholeNumbers(fiveOrMore);

        assertEquals(ValueSet.wholeNumbers(fiveOrMore.others()), otherSideOf(runs));
    }
}
