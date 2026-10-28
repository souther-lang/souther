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

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a list may be grown by where no row ran its element: the values that stand for the element,
 * the same with one more element where the element is a collection, a number a unit away from
 * those, and what the building of them met.
 *
 * <p>A value of {@code Huge} holds more elements than a proposal holds, so none is built, and that
 * is a figure the compiler declined at and not a type with no values.
 */
class ElementsOfATypeTest {

    /** How deep the nested records go. */
    private static final int DEPTH = 12;

    private static final String MODULE = """
            module p

            data Huge = List<Bool>
              invariant List.length(value) >= 65

            data N0 = { value: Int }
            """ + nested();

    /** {@code N1} holds two lists of {@code N0}, {@code N2} two lists of {@code N1}, and so on: a
     *  walk that goes into each of the two at every level goes into {@code N0} twice
     *  {@link #DEPTH} times over. */
    private static String nested() {
        StringBuilder out = new StringBuilder();
        for (int level = 1; level <= DEPTH; level++) {
            out.append("data N").append(level).append(" = { left: List<N").append(level - 1)
                    .append(">, right: List<N").append(level - 1).append("> }\n");
        }
        return out.toString();
    }

    private static final RuleReadingSource RULES = RuleReadings.ofSource(MODULE);

    private static final RuleReadingContext READING =
            RuleReadingContext.unshared(RULES, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);

    /** Builds the whole numbers and the lists of them, the fixtures these types are stood for by,
     *  and nothing else. */
    private static final Generator.CandidateCheck BUILDS = new Generator.CandidateCheck() {

        @Override
        public Built build(int parameter, FixtureTemplate candidate) {
            return new Built.NothingBuiltIt();
        }

        @Override
        public Optional<ObservedValue> builtAlone(Type type, FixtureTemplate candidate) {
            return read(candidate.text());
        }

        private Optional<ObservedValue> read(String text) {
            if (text.startsWith("[") && text.endsWith("]")) {
                String inside = text.substring(1, text.length() - 1);
                List<ObservedValue> elements = new ArrayList<>();
                if (!inside.isBlank()) {
                    for (String each : inside.split(", ")) {
                        Optional<ObservedValue> element = read(each);
                        if (element.isEmpty()) {
                            return Optional.empty();
                        }
                        elements.add(element.get());
                    }
                }
                return Optional.of(new ObservedValue.Sequence(elements));
            }
            try {
                return Optional.of(new ObservedValue.Integer(Long.parseLong(text)));
            } catch (NumberFormatException notANumber) {
                return Optional.empty();
            }
        }
    };

    /** What was asked for, so that how much of the types was gone into can be said. */
    private static final class Asked {
        final List<Type> representatives = new ArrayList<>();
        final List<Type> withOneElement = new ArrayList<>();
    }

    private static ElementsOfAType.Elements elementsOf(Type element, Asked asked) {
        return ElementsOfAType.of(type -> {
            asked.representatives.add(type);
            return Partitions.representativesHolding(type, READING,
                    FieldDomains.ConstructionLimits.NONE);
        }, type -> {
            asked.withOneElement.add(type);
            return ElementsOfAType.withOneElement(type, READING);
        }, READING, BUILDS, element);
    }

    private static ElementsOfAType.Elements elementsOf(Type element) {
        return elementsOf(element, new Asked());
    }

    private static Type named(String name) {
        return Type.ref(TypeSymbols.declared(new TypeKey(RULES.symbols().module(), name)));
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
     *  element in it, and that element a unit away. */
    @Test
    void aListIsOfferedEmptyAndWithAnElementAndTheElementAUnitAway() {
        ElementsOfAType.Elements elements = elementsOf(Type.list(Type.INT));

        assertTrue(elements.values().containsAll(List.of(listOf(), listOf(whole(0)),
                listOf(whole(1)), listOf(whole(-1)))), elements.values().toString());
        assertTrue(elements.met().nothing());
    }

    /** What stopped the values of the element inside the element is what the elements met. */
    @Test
    void whatStoppedTheValuesOfAnElementsElementIsMetByTheElement() {
        ElementsOfAType.Elements elements = elementsOf(Type.list(named("Huge")));

        assertEquals(List.of(listOf()), elements.values());
        assertEquals(Set.of(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS), elements.met().figures());
    }

    /**
     * The types are asked about once, however deep the element goes.
     *
     * <p>A walk into each field of a value, asking for the values of the element of each list it
     * finds, asks about {@code N0} twice for every level above it: past anything a search is given
     * to spend, before it has a first candidate to try.
     */
    @Test
    void theTypesAreAskedAboutOnceHoweverDeepTheElementGoes() {
        Asked asked = new Asked();

        ElementsOfAType.Elements elements = elementsOf(named("N" + DEPTH), asked);

        assertEquals(List.of(named("N" + DEPTH)), asked.representatives);
        assertEquals(List.of(named("N" + DEPTH)), asked.withOneElement);
        assertTrue(elements.met().nothing(), elements.met().toString());
    }
}
