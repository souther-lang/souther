package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;
import souther.compiler.values.AdmissibleValues;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.lang.reflect.RecordComponent;
import java.math.BigDecimal;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A state holding nothing, whichever of its domains is the one that holds nothing.
 *
 * <p>A clause reaches whatever domain has a word for it, and the domains do not overlap: a relation
 * between numbers reaches the interval algebra and says nothing to the facts, and a predicate about
 * a string reaches the facts and says nothing to the numbers. So a contradiction can be held
 * entirely by one of them while every other one is untouched, and a reader asking a single domain
 * whether a value exists answers yes whenever it asked the domain that had never heard of the rules.
 *
 * <p>Each domain is put at its own bottom on its own here, because that is the shape of the mistake:
 * not that the answer was wrong about a state where everything contradicts, but that it was wrong
 * about a state where one thing does.
 */
class WhetherAValueExistsIsAskedOfEveryDomainTest {

    private static final Term.Interner NAMES = new Term.Interner();
    private static final Term A_PREDICATE = NAMES.written("some predicate");
    private static final Term A_POSITION = NAMES.written("some position");

    /** Nothing taken in leaves every value there was. */
    @Test
    void aStateNothingWasTakenIntoHoldsWhateverItHeld() {
        assertFalse(ConstraintState.top().isBottom());
    }

    /** Numbers that cannot both hold, which is the one the reading always asked. */
    @Test
    void numbersThatCannotBothHoldLeaveNothing() {
        assertTrue(numbersAtBottom().isBottom());
        assertFalse(numbersAtBottom().facts().isBottom(), "and the other domain is untouched");
    }

    /** A predicate settled both ways, which reaches no number at all. */
    @Test
    void aPredicateSettledBothWaysLeavesNothing() {
        assertTrue(factsAtBottom().isBottom());
        assertFalse(factsAtBottom().numbers().isBottom(), "and the other domain is untouched");
    }

    /** A position left no value it may hold, which no number and no predicate has a word for. */
    @Test
    void aPositionWithNoValueLeftLeavesNothing() {
        assertTrue(valuesAtBottom().isBottom());
        assertFalse(valuesAtBottom().numbers().isBottom(), "and the other domains are untouched");
        assertFalse(valuesAtBottom().facts().isBottom());
    }

    private static ConstraintState numbersAtBottom() {
        // `1 <= 0`, which is how a reading already says that what it stands in is never reached.
        return ConstraintState.top()
                .taking(LinearForm.constant(BigDecimal.ONE), Rel.LE, Map.of());
    }

    private static ConstraintState factsAtBottom() {
        return ConstraintState.top().taking(A_PREDICATE, true).taking(A_PREDICATE, false);
    }

    private static ConstraintState valuesAtBottom() {
        return ConstraintState.top()
                .taking(AdmissibleValues.at(A_POSITION, ValueSet.just(Value.text("A"))))
                .taking(AdmissibleValues.at(A_POSITION, ValueSet.just(Value.text("B"))));
    }

    /**
     * A tripwire and not the proof above it.
     *
     * <p>What the tests above establish is that {@link ConstraintState#isBottom} reads each domain
     * this state has today. They cannot establish it of a domain added tomorrow, and the failure
     * they would leave is the silent one: the new domain reaches its own bottom, nothing asks it,
     * and every type whose rules only that domain can read is built. So the count is pinned here.
     * A domain added to the state fails this until it is added to the table above as well.
     */
    @Test
    void everyDomainOfTheStateIsOneThisTestPutAtItsOwnBottom() {
        RecordComponent[] domains = ConstraintState.class.getRecordComponents();
        assertEquals(3, domains.length,
                "each domain of the state needs a case above putting that one, and only that one, "
                        + "at its bottom");
    }

    /** And the interval algebra's own answer is left as it was: a state is not bottom because some
     * domain in it has nothing to say. */
    @Test
    void aDomainWithNothingToSayIsNotADomainThatHoldsNothing() {
        assertFalse(NumericDomain.<Term>top().isBottom());
    }
}
