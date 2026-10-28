package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a list may be grown by where no row ran its element: the values that stand for the element,
 * a number a unit away, the values with one more element in a list they hold, and what the
 * building of them met.
 *
 * <p>A value of {@code Huge} holds more elements than a proposal holds, so none is built, and that
 * is a figure the compiler declined at and not a type with no values.
 */
class ElementsOfATypeTest {

    private static final String MODULE = """
            module p

            data Huge = List<Bool>
              invariant List.length(value) >= 65
            """;

    private static final RuleReadingSource RULES = RuleReadings.ofSource(MODULE);

    private static final RuleReadingContext READING =
            RuleReadingContext.unshared(RULES, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);

    /** Builds the whole numbers and the empty list, the two fixtures these types are stood for by,
     *  and nothing else. */
    private static final Generator.CandidateCheck BUILDS = new Generator.CandidateCheck() {

        @Override
        public Built build(int parameter, FixtureTemplate candidate) {
            return new Built.NothingBuiltIt();
        }

        @Override
        public Optional<ObservedValue> builtAlone(Type type, FixtureTemplate candidate) {
            if (candidate.text().equals("[]")) {
                return Optional.of(new ObservedValue.Sequence(List.of()));
            }
            try {
                return Optional.of(new ObservedValue.Integer(Long.parseLong(candidate.text())));
            } catch (NumberFormatException notANumber) {
                return Optional.empty();
            }
        }
    };

    private static ElementsOfAType.Elements elementsOf(Type element) {
        return ElementsOfAType.of(type -> Partitions.representativesHolding(type, READING,
                FieldDomains.ConstructionLimits.NONE), READING, BUILDS, element);
    }

    private static ObservedValue whole(long n) {
        return new ObservedValue.Integer(n);
    }

    private static ObservedValue listOf(ObservedValue... elements) {
        return new ObservedValue.Sequence(List.of(elements));
    }

    @Test
    void aNumberIsOfferedWithTheNumbersAUnitAway() {
        ElementsOfAType.Elements elements = elementsOf(Type.INT);

        assertTrue(elements.values().containsAll(List.of(whole(0), whole(1), whole(-1))),
                elements.values().toString());
        assertTrue(elements.met().nothing());
    }

    /** An empty list is the same at an empty list as at none, so the list is offered with an
     *  element in it, built of the element's own values. */
    @Test
    void aListIsOfferedEmptyAndWithAnElement() {
        ElementsOfAType.Elements elements = elementsOf(Type.list(Type.INT));

        assertTrue(elements.values().contains(listOf()), elements.values().toString());
        assertTrue(elements.values().contains(listOf(whole(0))), elements.values().toString());
        assertTrue(elements.met().nothing());
    }

    /** What stopped the values of the element inside the element is what the elements met. */
    @Test
    void whatStoppedTheValuesOfAnElementsElementIsMetByTheElement() {
        ElementsOfAType.Elements elements = elementsOf(Type.list(Type.ref(
                TypeSymbols.declared(new TypeKey(RULES.symbols().module(), "Huge")))));

        assertEquals(List.of(listOf()), elements.values());
        assertEquals(Set.of(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS), elements.met().figures());
    }
}
