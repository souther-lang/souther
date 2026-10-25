package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.Position;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A rule asking a map for an entry under the key standing in another field is a rule of the two
 * fields together, and is read at both.
 *
 * <p>{@code Map.containsKey(base, rates)}, and the lookup {@code Map.get(base, rates)} followed to
 * a comparison of what it found with a written number, absent counting as false. Read as a form
 * nothing takes apart, the rule left a question standing at both fields.
 */
class AMapAskedForAnEntryUnderAKeyBesideItIsReadTest {

    private static final String BEHAVIOR = """

            behavior probe : (n: N) -> Int
            let probe (n) = if Map.size(n.rates) >= 0 then 1 else 2
            """;

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
                """.formatted(fields, invariant, helper) + BEHAVIOR;
    }

    private static final String BASE_THEN_RATES =
            "base: CurrencyCode, rates: Map<CurrencyCode, ConversionRate>";

    private static String lookup(String comparison) {
        return """
                let baseAtRate (base: CurrencyCode, rates: Map<CurrencyCode, ConversionRate>): Bool =
                    Map.get(base, rates)
                        |> Option.map(r -> %s)
                        |> Option.withDefault(false)
                """.formatted(comparison);
    }

    @Test
    void aMembershipTestIsReadAtTheKeyAndTheMap() {
        assertEquals(Map.of("n.base", List.of(), "n.rates", List.of()),
                unansweredAtTheFields(table(BASE_THEN_RATES, "Map.containsKey(base, rates)", "")));
    }

    @Test
    void aLookupComparedWithAWrittenNumberIsReadAtTheKeyAndTheMap() {
        String model = table(BASE_THEN_RATES, "baseAtRate(base, rates)",
                lookup("Decimal.compare(r.value, 1.0m) == 0"));

        assertEquals(Map.of("n.base", List.of(), "n.rates", List.of()),
                unansweredAtTheFields(model));
    }

    @Test
    void aLookupThatOnlyBoundsTheValueFoundStaysUnanswered() {
        String model = table(BASE_THEN_RATES, "baseAtRate(base, rates)",
                lookup("Decimal.compare(r.value, 1.0m) >= 0"));

        Map<String, List<String>> left = unansweredAtTheFields(model);

        assertFalse(left.get("n.base").isEmpty(),
                "a builder told the entry exists would build maps the rule refuses");
        assertFalse(left.get("n.rates").isEmpty());
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

    /**
     * Two entries asked of one map, each under a key of its own and a number of its own, are read
     * at every field, the number being handed to a helper as an argument.
     */
    @Test
    void twoEntriesAskedOfOneMapAreReadAtTheKeysAndTheMap() {
        assertEquals(Map.of("n.x", List.of(), "n.y", List.of(), "n.rates", List.of()),
                unansweredAtTheFields(TWO_ENTRIES + BEHAVIOR));
    }

    /**
     * A rule of the record that was listed and nothing was made of may ask the same map the
     * opposite: {@code key} held in the map and the key {@code 0} not, which no map beside a key of
     * nought satisfies. Listing a rule is not reading it, and the entry asked for is not built
     * beside it.
     */
    @Test
    void aRuleOfTheRecordNothingWasMadeOfLeavesTheMapUnanswered() {
        Map<String, List<String>> left = unansweredAtTheFields("""
                module demo

                data N = { key: Int, rates: Map<Int, Int> }
                    invariant held = Map.containsKey(key, rates)
                    invariant notNought = Bool.not(Map.containsKey(0, rates))

                behavior probe : (n: N) -> Int
                let probe (n) = if Map.size(n.rates) >= 0 then 1 else 2
                """);

        assertFalse(left.get("n.key").isEmpty(), "a key of nought has no map beside it");
        assertFalse(left.get("n.rates").isEmpty(), "a rule asking the map the opposite is unread");
    }

    /**
     * A key that is not a field of the record is a key the builders are never told of, because a
     * record's fields are chosen one at a time and a key is chosen before the map it is a key of.
     * The rule is left standing rather than called read.
     */
    @Test
    void aKeyThatIsNotAFieldOfTheRecordLeavesTheMapUnanswered() {
        Map<String, List<String>> left = unansweredAtTheFields("""
                module demo

                data Inner = { k: String }
                data N = { inner: Inner, rates: Map<String, Int> }
                    invariant has = Map.containsKey(inner.k, rates)
                """ + BEHAVIOR);

        assertFalse(left.get("n.rates").isEmpty(), "nothing builds a map for a key it cannot reach");
    }

    /** What stands unanswered at each field of the input of {@code probe}, by field. */
    private static Map<String, List<String>> unansweredAtTheFields(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingContext reading = RuleReadingContext.unshared(
                RuleReadings.of(compilation, module), ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        Map<String, List<String>> out = new LinkedHashMap<>();
        for (Position each : InputDomain.of(sigs.get("probe"), reading,
                TypeCardinality.Counts.workedOutIn(reading), Membership.none()).positions()) {
            String path = each.path().toString();
            if (path.startsWith("n.") && path.indexOf('.', 2) < 0 && !path.contains("[")) {
                out.put(path, each.unansweredQuestions().stream()
                        .map(question -> question.rule().toString()).toList());
            }
        }
        return out;
    }
}
