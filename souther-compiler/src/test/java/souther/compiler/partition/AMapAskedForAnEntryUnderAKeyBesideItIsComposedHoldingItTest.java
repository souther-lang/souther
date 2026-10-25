package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.Symbols;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A record whose rules ask a map for an entry under the key standing in another field is composed
 * with the map holding that entry, and the key is chosen first whichever field is written first.
 *
 * <p>Each field was chosen on its own against the rules, so a key and a map met only where the key
 * happened to be a key of the map. The entry the rule asks for is the one under the key that was
 * chosen, and when it asks for the value under it the value is the number it names.
 */
class AMapAskedForAnEntryUnderAKeyBesideItIsComposedHoldingItTest {

    private static final String BASE_THEN_RATES =
            "base: CurrencyCode, rates: Map<CurrencyCode, ConversionRate>";

    private static final String RATES_THEN_BASE =
            "rates: Map<CurrencyCode, ConversionRate>, base: CurrencyCode";

    private static String table(String fields, String invariant, String helper) {
        return """
                module demo

                data CurrencyCode = String
                    invariant String.matches("[A-Z]{3}", value)
                data ConversionRate = Decimal
                    invariant value > 0.0m

                data N = { %s }
                    invariant baseIsUnity = %s

                %s
                """.formatted(fields, invariant, helper);
    }

    private static String atRate(String comparison) {
        return """
                let baseAtRate (base: CurrencyCode, rates: Map<CurrencyCode, ConversionRate>): Bool =
                    Map.get(base, rates)
                        |> Option.map(r -> %s)
                        |> Option.withDefault(false)
                """.formatted(comparison);
    }

    @Test
    void aMembershipTestHasTheMapHoldTheKeyChosenAndNoOtherEntry() {
        Partitions.FieldsChosen chosen =
                composed(table(BASE_THEN_RATES, "Map.containsKey(base, rates)", ""));

        assertEquals("CurrencyCode(\"AAA\")", chosen.fields().get("base").text());
        assertEquals("[(CurrencyCode(\"AAA\"), ConversionRate(1m))]",
                chosen.fields().get("rates").text());
    }

    @Test
    void aLookupComparedWithAWrittenNumberHasTheEntryHoldThatNumber() {
        Partitions.FieldsChosen chosen = composed(table(BASE_THEN_RATES, "baseAtRate(base, rates)",
                atRate("Decimal.compare(r.value, 2.5m) == 0")));

        assertEquals("[(CurrencyCode(\"AAA\"), ConversionRate(2.5m))]",
                chosen.fields().get("rates").text());
    }

    @Test
    void theKeyIsChosenFirstWhicheverFieldIsWrittenFirst() {
        Partitions.FieldsChosen chosen = composed(table(RATES_THEN_BASE, "baseAtRate(base, rates)",
                atRate("Decimal.compare(r.value, 2.5m) == 0")));

        assertEquals(List.of("rates", "base"), List.copyOf(chosen.fields().keySet()),
                "the record is written in the order it declares its fields");
        assertEquals("CurrencyCode(\"AAA\")", chosen.fields().get("base").text());
        assertEquals("[(CurrencyCode(\"AAA\"), ConversionRate(2.5m))]",
                chosen.fields().get("rates").text());
    }

    private static final String TWO_ENTRIES = """
            module demo

            data N = { x: String, y: String, rates: Map<String, Int> }
                invariant atX = atKey(x, rates, 1)
                invariant atY = atKey(y, rates, 2)

            let atKey (k: String, m: Map<String, Int>, n: Int): Bool =
                Map.get(k, m)
                    |> Option.map(r -> r == n)
                    |> Option.withDefault(false)
            """;

    /** Two entries asked of one map under two keys are both in the map built. */
    @Test
    void aMapAskedForTwoEntriesHoldsBothOfThem() {
        Partitions.FieldsChosen chosen = composedGiven(TWO_ENTRIES,
                Map.of("x", FixtureTemplate.string("a"), "y", FixtureTemplate.string("b")));

        String rates = chosen.fields().get("rates").text();
        assertTrue(rates.contains("(\"a\", 1)"), rates);
        assertTrue(rates.contains("(\"b\", 2)"), rates);
    }

    /**
     * Two keys asked for two numbers are chosen apart, whatever each would have been alone.
     *
     * <p>Chosen on their own both are the first string there is, and a map cannot hold two numbers
     * under it. That the first choice collides is no reason the type has no such map, so the key
     * chosen second passes over the one chosen first.
     */
    @Test
    void keysAskedForDifferentNumbersAreChosenApart() {
        Partitions.FieldsChosen chosen = composed(TWO_ENTRIES);

        String x = chosen.fields().get("x").text();
        String y = chosen.fields().get("y").text();
        assertTrue(!x.equals(y), x + " and " + y + " are one key");
        String rates = chosen.fields().get("rates").text();
        assertTrue(rates.contains("(" + x + ", 1)"), rates);
        assertTrue(rates.contains("(" + y + ", 2)"), rates);
    }

    private static final String POSITIVE_RATES = """
            module demo

            data Rate = Decimal
                invariant value > 0.0m

            data N = { base: String, rates: Map<String, Rate> }
                invariant atNought = atRate(base, rates)

            let atRate (k: String, rates: Map<String, Rate>): Bool =
                Map.get(k, rates)
                    |> Option.map(r -> Decimal.compare(r.value, 0.0m) == 0)
                    |> Option.withDefault(false)
            """;

    /**
     * A number the value's type does not admit is not written under the name and offered: the map
     * would hold a rate the type refuses, and there is no map the rule asks for.
     */
    @Test
    void aNumberTheValueTypeRefusesIsNotWrittenUnderItsName() {
        assertNull(composedGiven(POSITIVE_RATES, Map.of()).fields());
    }

    private static String rateSet(String asked) {
        return """
                module demo

                data Rate = Decimal
                    invariant value == 1.0m || value == 3.0m

                data N = { base: String, rates: Map<String, Rate> }
                    invariant atRate = atRate(base, rates)

                let atRate (k: String, rates: Map<String, Rate>): Bool =
                    Map.get(k, rates)
                        |> Option.map(r -> Decimal.compare(r.value, %s) == 0)
                        |> Option.withDefault(false)
                """.formatted(asked);
    }

    /**
     * A number inside the range the value type leaves and outside the set it admits is not
     * written under the name: the range of one or three holds two, and the type does not.
     */
    @Test
    void aNumberBetweenTheOnesTheValueTypeAdmitsIsNotWrittenUnderItsName() {
        assertNull(composedGiven(rateSet("2.0m"), Map.of()).fields());
        assertTrue(composedGiven(rateSet("3.0m"), Map.of()).fields().get("rates").text()
                .contains("Rate(3m)"));
    }

    /**
     * Two numbers asked of one key are no map at all, and the record is not composed: choosing the
     * map as any other would be offering one the rules refuse.
     */
    @Test
    void aMapAskedForTwoNumbersUnderOneKeyIsNotBuilt() {
        Partitions.FieldsChosen chosen = composedGiven(TWO_ENTRIES,
                Map.of("x", FixtureTemplate.string("a"), "y", FixtureTemplate.string("a")));

        assertNull(chosen.fields(), "no map holds both a one and a two under the key a");
    }

    private static Partitions.FieldsChosen composed(String source) {
        Partitions.FieldsChosen chosen = composedGiven(source, Map.of());
        assertNotNull(chosen.fields(), "the record is one something can be composed of");
        return chosen;
    }

    private static Partitions.FieldsChosen composedGiven(String source,
                                                         Map<String, FixtureTemplate> given) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        TypeSymbol.AtModule record = TypeSymbols.declared(new TypeKey(symbols.module(), "N"));
        RuleReadingContext reading = RuleReadingContext.unshared(
                RuleReadings.of(compilation, "demo"), ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        return Partitions.fieldsOf(record, record, reading, Set.of(), given);
    }
}
