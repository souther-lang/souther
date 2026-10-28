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
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a list may be grown by where no row ran its element: the values that stand for the element,
 * the same with one more element where the element is a collection, a number a unit away from
 * those, and a list grown in a list already made, each made as far as it is asked for.
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

            data Bag = List<Int>
            data Sack = Bag

            data N0 = { value: Int }
            """ + nested();

    /** {@code N1} holds two lists of {@code N0}, {@code N2} two lists of {@code N1}, and so on. */
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

    /** What was asked for and what was said, so that how much of the types was gone into can be
     *  told. */
    private static final class Seen implements ElementsOfAType.Stops {
        final List<Type> representatives = new ArrayList<>();
        final List<Type> withOneElement = new ArrayList<>();
        final Set<CompositionBudget> figures = new HashSet<>();
        final List<Integer> limits = new ArrayList<>();

        @Override
        public void met(CompositionShortfall shortfall) {
            figures.addAll(shortfall.figures());
        }

        @Override
        public void limitedAt(int most) {
            limits.add(most);
        }
    }

    private static ElementsOfAType elements(int most, Seen seen) {
        return new ElementsOfAType(type -> {
            seen.representatives.add(type);
            return Partitions.representativesHolding(type, READING,
                    FieldDomains.ConstructionLimits.NONE);
        }, type -> {
            seen.withOneElement.add(type);
            return ElementsOfAType.withOneElement(type, READING);
        }, READING, BUILDS, most, seen);
    }

    private static List<ObservedValue> first(int many, Type element, ElementsOfAType elements) {
        List<ObservedValue> out = new ArrayList<>();
        for (Iterator<ObservedValue> each = elements.of(element);
             out.size() < many && each.hasNext(); ) {
            out.add(each.next());
        }
        return out;
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
        List<ObservedValue> values = first(10, Type.INT, elements(64, new Seen()));

        assertEquals(List.of(whole(0), whole(1), whole(-1)), values);
    }

    /** An empty list is the same at an empty list as at none, so the list is offered with an
     *  element in it, and that element a unit away. */
    @Test
    void aListIsOfferedEmptyAndWithAnElementAndTheElementAUnitAway() {
        List<ObservedValue> values = first(20, Type.list(Type.INT), elements(64, new Seen()));

        assertTrue(values.containsAll(List.of(listOf(), listOf(whole(0)), listOf(whole(1)),
                listOf(whole(-1)))), values.toString());
    }

    /** A list in a list in a list is grown in the list that was grown, as far as it is asked. */
    @Test
    void aListIsGrownInTheListThatWasGrown() {
        List<ObservedValue> values = first(30, Type.list(Type.list(Type.INT)),
                elements(64, new Seen()));

        assertTrue(values.contains(listOf(listOf(whole(0)))), values.toString());
        assertTrue(values.contains(listOf(listOf(whole(1)))), values.toString());
    }

    /** Asked for one value, the proposals of the element are asked for and nothing past the first
     *  that gave one. */
    @Test
    void aValueIsMadeOnlyWhenItIsAskedFor() {
        Seen seen = new Seen();
        Type list = Type.list(Type.INT);

        List<ObservedValue> values = first(1, list, elements(64, seen));

        assertEquals(List.of(listOf()), values);
        assertEquals(List.of(list), seen.representatives);
        assertEquals(List.of(), seen.withOneElement);
    }

    /**
     * However deep the element goes, the types are asked about once each, and asked for every
     * value there is: a walk into each field of a value, asking for the values of the element of
     * each list it finds, asks about {@code N0} twice for every level above it.
     */
    @Test
    void aTypeIsAskedAboutOnceHoweverDeepItGoes() {
        Seen seen = new Seen();
        Type deepest = named("N" + DEPTH);

        first(1000, deepest, elements(64, seen));

        assertEquals(List.of(deepest), seen.representatives);
        assertEquals(List.of(deepest), seen.withOneElement);
    }

    /**
     * The values of a type whose lists can all be filled come to an end, and the end is not said to
     * be a bound: a body that answers the constant was asked every one of them and none told it
     * apart, which is not the same as having stopped short.
     */
    @Test
    void theValuesOfATypeThatDoesNotHoldItselfComeToAnEnd() {
        Seen seen = new Seen();

        List<ObservedValue> values = first(1000, Type.list(Type.list(Type.list(Type.INT))),
                elements(64, seen));

        assertTrue(values.size() < 64, values.toString());
        assertEquals(List.of(), seen.limits);
        assertTrue(values.contains(listOf(listOf(listOf(whole(0))))), values.toString());
    }

    /** Past what the bound lets be made, nothing more is, and the bound is said. */
    @Test
    void theValuesOfATypeAreBoundedAndTheBoundIsSaid() {
        Seen seen = new Seen();
        ElementsOfAType elements = elements(3, seen);

        List<ObservedValue> values = first(100, Type.list(Type.list(Type.INT)), elements);

        assertEquals(3, values.size());
        assertEquals(List.of(3), seen.limits);
    }

    /** What stopped the values of the element inside the element is said. */
    @Test
    void whatStoppedTheValuesOfAnElementsElementIsSaid() {
        Seen seen = new Seen();

        List<ObservedValue> values = first(100, Type.list(named("Huge")), elements(64, seen));

        assertEquals(List.of(listOf()), values);
        assertEquals(Set.of(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS), seen.figures);
    }

    /** The collection of one stands inside the names the position wears: a {@code Bag} is not
     *  a list. */
    @Test
    void aCollectionOfOneWearsTheNamesOfThePosition() {
        assertEquals(List.of("Bag([0])"), ElementsOfAType.withOneElement(named("Bag"), READING)
                .values().stream().map(FixtureTemplate::text).toList());
        assertEquals(List.of("Sack(Bag([0]))"), ElementsOfAType.withOneElement(named("Sack"),
                READING).values().stream().map(FixtureTemplate::text).toList());
        assertEquals(List.of(), ElementsOfAType.withOneElement(Type.INT, READING).values());
    }
}
