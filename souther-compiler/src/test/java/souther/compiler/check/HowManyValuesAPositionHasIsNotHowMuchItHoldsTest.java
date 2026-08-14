package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.numeric.Cardinality;
import souther.compiler.query.Compilation;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.TypeName;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two readings of one set of rules, and what tells them apart.
 *
 * <p>A set of two asks its element for two values that differ. The floor is a count of what the set
 * holds and the two values are a count of what the element is, and both are read off the same numbers
 * — so a reader with one answer for both would meet the floor by counting the element's values and
 * fill the set from a rule about its size.
 */
class HowManyValuesAPositionHasIsNotHowMuchItHoldsTest {

    private static Hir.Data data(Compilation compilation, String name) {
        for (Hir.Def def : compilation.module("demo").defs()) {
            if (def instanceof Hir.Data found && found.name().equals(name)) {
                return found;
            }
        }
        throw new IllegalArgumentException("no such declaration: " + name);
    }

    private static Cardinality valuesAt(String source, String name, String path) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        // A rule nothing could type is a rule nothing reads, and a row resting on one is answered by
        // the absence of the rule rather than by anything this decides.
        assertEquals(java.util.List.of(), compilation.diagnostics().values().stream()
                        .flatMap(java.util.List::stream)
                        .map(each -> each.diagnostic().code().toString()).toList(),
                "the model this reads has to be one somebody could write");
        Symbols symbols = compilation.symbols("demo");
        return OccurrenceValues.of(TypeSymbols.declared(new TypeKey(symbols.module(), name)), data(compilation, name), symbols)
                .wholeValuesAt(path);
    }

    @Test
    void aNumberBoundedToOneNumberIsOneValue() {
        assertEquals(Cardinality.atMost(1), valuesAt("""
                module demo

                data One = Int
                    invariant only = value >= 1 && value <= 1
                """, "One", FieldDomains.THE_VALUE));
    }

    @Test
    void aRangeIsAsManyValuesAsItHasNumbers() {
        assertEquals(Cardinality.atMost(10), valuesAt("""
                module demo

                data Ten = Int
                    invariant range = value >= 1 && value <= 10
                """, "Ten", FieldDomains.THE_VALUE));
    }

    @Test
    void anEndTheRangeStopsShortOfIsNotOneOfTheValues() {
        assertEquals(Cardinality.atMost(8), valuesAt("""
                module demo

                data Inner = Int
                    invariant range = value > 1 && value < 10
                """, "Inner", FieldDomains.THE_VALUE));
    }

    @Test
    void aFieldIsCountedWhereItSits() {
        assertEquals(Cardinality.atMost(3), valuesAt("""
                module demo

                data R = { n: Int }
                    invariant small = n >= 1 && n <= 3
                """, "R", "n"));
    }

    /** Open at an end, and there is no number of values to give. */
    @Test
    void aNumberBoundedOnOneSideOnlyIsNotCounted() {
        assertEquals(Cardinality.UNKNOWN, valuesAt("""
                module demo

                data Positive = Int
                    invariant up = value >= 1
                """, "Positive", FieldDomains.THE_VALUE));
        assertEquals(Cardinality.UNKNOWN, valuesAt("""
                module demo

                data Any = Int
                """, "Any", FieldDomains.THE_VALUE));
    }

    /**
     * The same two ends on a value spaced more finely than one apart. There are unboundedly many
     * decimals between one and ten, so the ends alone are not what makes a count — and the ends here
     * are the very ends the integer above was counted between.
     */
    @Test
    void valuesSpacedMoreFinelyThanOneApartAreNotCounted() {
        assertEquals(Cardinality.UNKNOWN, valuesAt("""
                module demo

                data Money = Decimal
                    invariant range = value >= 1.0m && value <= 10.0m
                """, "Money", FieldDomains.THE_VALUE));
        assertEquals(Cardinality.atMost(10), valuesAt("""
                module demo

                data Ten = Int
                    invariant range = value >= 1 && value <= 10
                """, "Ten", FieldDomains.THE_VALUE), "and the integer between them still is");
    }

    /**
     * A floor on what a set holds is not a count of what the set is. Read as one, an element bounded
     * to a single value would answer the set's own rule.
     */
    @Test
    void aFloorOnWhatIsHeldIsNotACountOfValues() {
        String source = """
                module demo

                data Pair = Set<Int>
                    invariant two = Set.size(value) >= 2
                """;
        assertEquals(Cardinality.UNKNOWN, valuesAt(source, "Pair", FieldDomains.THE_VALUE));
    }
}
