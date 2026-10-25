package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.Position;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A rule saying a place is a number made of other places says nothing about any one of those, and
 * once they stand at numbers the place stands at what they come to.
 *
 * <p>{@code net == Decimal.round(2, HALF_UP, quantity * price * (1 - discount))} states what
 * {@code net} is beside the other three and leaves each of them every value its own type admits.
 * Read as a rule about a product the arithmetic has no line for, it left a question standing at each
 * of the three, and composing a row did not know {@code net} followed from them.
 */
class APlaceDefinedAsANumberMadeOfOthersLeavesThemFreeTest {

    private static final String BEHAVIOR = """

            behavior probe : (n: N) -> Int
            let probe (n) = 1
            """;

    private static final String QUOTE_LINE = """
            module demo

            data Quantity = Int
                invariant value >= 1
            data UnitPrice = Decimal
                invariant value >= 0.0m
            data DiscountRate = Decimal
                invariant value >= 0.0m && value <= 0.5m
            data Amount = Decimal
                invariant value >= 0.0m

            data N =
                { quantity: Quantity
                , listPrice: UnitPrice
                , discount: DiscountRate
                , net: Amount
                }
                invariant Decimal.compare(net.value,
                    Decimal.round(2, HALF_UP, Decimal.fromInt(quantity.value) * listPrice.value
                                  * (1.0m - discount.value))) == 0
            """;

    private static String record(String invariant) {
        return """
                module demo

                data N = { a: Int, b: Int, c: Int }
                    invariant %s
                """.formatted(invariant);
    }

    private static final String ROUNDED_PRODUCT = """
            module demo

            data N = { x: Decimal, y: Decimal, c: Decimal }
                invariant Decimal.compare(c, Decimal.round(2, HALF_UP, x * y)) == 0
            """;

    @Test
    void everyPlaceOfAQuoteLineIsAnswered() {
        assertEquals(Map.of("n.quantity", List.of(), "n.listPrice", List.of(),
                        "n.discount", List.of(), "n.net", List.of()),
                unansweredBelowTheInput(QUOTE_LINE + BEHAVIOR));
    }

    @Test
    void aProductBesideAPlaceThatItDefinesIsTakenInAtTheFactors() {
        assertEquals(Map.of("n.a", List.of(), "n.b", List.of(), "n.c", List.of()),
                unansweredBelowTheInput(record("c == a * b") + BEHAVIOR));
    }

    @Test
    void aProductThatDefinesNoPlaceStaysUnanswered() {
        Map<String, List<String>> left = unansweredBelowTheInput(record("a * b >= 3") + BEHAVIOR);

        assertFalse(left.get("n.a").isEmpty(), "the product bounds the two together");
        assertFalse(left.get("n.b").isEmpty());
    }

    @Test
    void aPlaceMadeOfItselfIsNoDefinitionOfIt() {
        Map<String, List<String>> left = unansweredBelowTheInput(record("a == a * b") + BEHAVIOR);

        assertFalse(left.get("n.b").isEmpty(), "what b may be depends on a, and a on b");
    }

    @Test
    void aNumberMadeOfWhatThisDoesNotReadStaysUnanswered() {
        Map<String, List<String>> left =
                unansweredBelowTheInput(record("c == a * Int.floorMod(b, 7)") + BEHAVIOR);

        assertFalse(left.get("n.a").isEmpty(), "a remainder is not arithmetic this evaluates");
    }

    @Test
    void theDefinedPlaceStandsAtTheRoundedProductOnceTheFactorsDo() {
        assertDefinedAt("0.01", Map.of("x", "0.5", "y", "0.01"));
        assertDefinedAt("0", Map.of("x", "0.4", "y", "0.01"));
        assertDefinedAt("0.01", Map.of("x", "0.6", "y", "0.01"));
        assertDefinedAt("1.23", Map.of("x", "123", "y", "0.01"));
    }

    @Test
    void aHalfStepBelowNoughtRoundsAwayFromNought() {
        assertDefinedAt("-0.01", Map.of("x", "-0.5", "y", "0.01"));
        assertDefinedAt("0", Map.of("x", "-0.4", "y", "0.01"));
    }

    @Test
    void theDefinedPlaceIsLeftWhereItWasWhileAFactorIsFree() {
        NumericDomain.Bounds beside = fieldsOf(ROUNDED_PRODUCT).composing(FieldDomains.atValues(
                Map.of(RuleKey.of("x"), new Count(new BigDecimal("0.5")))))
                .at(RuleKey.of("c")).values();

        assertNull(pointOf(beside), "with y still free there is no one number c comes to");
    }

    private static void assertDefinedAt(String expected, Map<String, String> factors) {
        Map<RuleKey, Count> fixed = new LinkedHashMap<>();
        factors.forEach((name, number) ->
                fixed.put(RuleKey.of(name), new Count(new BigDecimal(number))));

        NumericDomain.Bounds bounds = fieldsOf(ROUNDED_PRODUCT).composing(FieldDomains.atValues(fixed))
                .at(RuleKey.of("c")).values();

        BigDecimal at = pointOf(bounds);
        assertNotNull(at, () -> "c stands at one number under " + factors + " and not at " + bounds);
        assertEquals(0, new BigDecimal(expected).compareTo(at),
                () -> "under " + factors + " c is " + at + " and not " + expected);
    }

    /** The one number {@code bounds} holds, or null where it holds more than one. */
    private static BigDecimal pointOf(NumericDomain.Bounds bounds) {
        if (bounds == null || bounds.min() == null || bounds.max() == null) {
            return null;
        }
        BigDecimal low = Count.number(bounds.min().at()).at();
        BigDecimal high = Count.number(bounds.max().at()).at();
        return low.compareTo(high) == 0 ? low : null;
    }

    private static FieldDomains fieldsOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                .flatMap(List::stream).map(each -> each.diagnostic().code()).toList(),
                "the model this reads has to be one somebody could write");
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        TypeSymbol.AtModule name = TypeSymbols.declared(new TypeKey(symbols.module(), "N"));
        return FieldDomains.of(name, RuleReadingContext.unshared(
                RuleReadings.of(compilation, "demo"), ReadAs.THE_COMPILATION_DOES, TestDay.TODAY));
    }

    /** What stands unanswered at each place below the input of {@code probe}, by place. */
    private static Map<String, List<String>> unansweredBelowTheInput(String source) {
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
            if (path.startsWith("n.")) {
                out.put(path, each.unansweredQuestions().stream()
                        .map(question -> question.rule().toString()).toList());
            }
        }
        return out;
    }
}
