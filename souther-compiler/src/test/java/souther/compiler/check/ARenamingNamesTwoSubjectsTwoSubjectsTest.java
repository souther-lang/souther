package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.OrderedIntervals;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;
import souther.compiler.values.AdmissibleValues;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.math.BigDecimal;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A state said in another vocabulary keeps two subjects two subjects.
 *
 * <p>Which is not what {@link NumericDomain#over} does. That is a fold: two atoms arriving at one
 * name are one number and their coefficients are added, because a caller writing
 * {@code List.length(xs) + Set.size(xs)} wrote two spellings of one count. Right of a form and wrong
 * of a state — two positions under one name would bound each other, hold each other's values and
 * settle each other's predicates, which is the reading saying what nobody wrote.
 *
 * <p><b>And the rule is about the whole vocabulary, not about each domain.</b> A subject may sit in
 * one domain and no other: a predicate the numbers have no word for, a position only an ordering
 * bounds. So a naming that is injective on every domain read by itself can still put two subjects
 * under one name, and nothing that sees one domain can tell. That is the case below, and it is the
 * one a check written per domain would let through.
 */
class ARenamingNamesTwoSubjectsTwoSubjectsTest {

    private static final Term.Interner NAMES = new Term.Interner();
    private static final FactSubject ONLY_IN_FACTS = FactSubject.of(NAMES.written("a predicate"));
    private static final FactSubject ONLY_IN_ORDERED = FactSubject.of(NAMES.written("a position"));
    private static final FactSubject ONLY_IN_VALUES = FactSubject.of(NAMES.written("another position"));
    private static final FactSubject ONLY_IN_NUMBERS = FactSubject.of(NAMES.written("a number"));

    /** Each of the four sits in one domain and no other, which is what makes the case. */
    @Test
    void eachSubjectIsHeldByOneDomainAlone() {
        ConstraintState<FactSubject> state = spread();
        assertTrue(state.facts().entails(ONLY_IN_FACTS, true));
        assertFalse(state.ordered().at(ONLY_IN_FACTS).holdsNothing());
        assertEquals(ValueSet.ANY, state.values().at(ONLY_IN_ORDERED));
    }

    /** Two subjects no one domain holds together, sent to one name. */
    @Test
    void twoSubjectsFromDifferentDomainsMayNotShareAName() {
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> spread().renamed(InjectiveRenaming.of(subject -> "one name")));

        assertTrue(refused.getMessage().contains("one subject"), refused.getMessage());
    }

    /** And a naming that keeps them apart is carried through every domain. */
    @Test
    void aNamingThatKeepsThemApartIsCarriedThrough() {
        Map<FactSubject, String> apart = Map.of(ONLY_IN_FACTS, "p.f", ONLY_IN_ORDERED, "p.o",
                ONLY_IN_VALUES, "p.v", ONLY_IN_NUMBERS, "p.n");
        ConstraintState<String> said = spread().renamed(InjectiveRenaming.of(apart::get));

        assertTrue(said.facts().entails("p.f", true));
        assertTrue(said.ordered().at("p.o").holdsNothing());
        assertEquals(ValueSet.just(Value.text("A")), said.values().at("p.v"));
        assertEquals(Endpoint.inclusive(Count.of(3)),
                said.numbers().boundsOf(LinearForm.<String>atom("p.n")).max());
    }

    /** A subject the naming sends to where it already was is that subject, not a second one. */
    @Test
    void aSubjectMayArriveAtItsOwnNameTwice() {
        assertEquals("x", InjectiveRenaming.<String, String>of(subject -> "x").apply("x"));
    }

    /** One subject in each domain, and no subject in two of them. */
    private static ConstraintState<FactSubject> spread() {
        return ConstraintState.<FactSubject>top()
                .taking(ONLY_IN_FACTS, true)
                .taking(OrderedIntervals.at(ONLY_IN_ORDERED,
                        new OrderedInterval(Endpoint.inclusive(Count.of(6)),
                                Endpoint.inclusive(Count.of(2)))))
                .takingValuesRead(
                        AdmissibleValues.at(ONLY_IN_VALUES, ValueSet.just(Value.text("A"))))
                .taking(LinearForm.<FactSubject>atom(ONLY_IN_NUMBERS)
                                .minus(LinearForm.<FactSubject>constant(BigDecimal.valueOf(3))),
                        Rel.LE, Map.of(ONLY_IN_NUMBERS, souther.compiler.numeric.Granularity.DISCRETE));
    }
}
