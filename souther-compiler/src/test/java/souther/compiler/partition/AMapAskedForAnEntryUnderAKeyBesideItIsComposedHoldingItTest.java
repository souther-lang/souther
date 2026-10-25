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

    private static Partitions.FieldsChosen composed(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        TypeSymbol.AtModule record = TypeSymbols.declared(new TypeKey(symbols.module(), "N"));
        RuleReadingContext reading = RuleReadingContext.unshared(
                RuleReadings.of(compilation, "demo"), ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        Partitions.FieldsChosen chosen =
                Partitions.fieldsOf(record, record, reading, Set.of(), Map.of());
        assertNotNull(chosen.fields(), "the record is one something can be composed of");
        return chosen;
    }
}
