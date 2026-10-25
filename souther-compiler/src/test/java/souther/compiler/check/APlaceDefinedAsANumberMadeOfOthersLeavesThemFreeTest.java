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
                unansweredBelowTheInput("""
                        module demo

                        data N = { a: Decimal, b: Decimal, c: Decimal }
                            invariant c == a * b
                        """ + BEHAVIOR));
    }

    /** Whole numbers stop at a width, and a product of two of them may not: no factor is free. */
    @Test
    void aProductOfWholeNumbersBesideAPlaceThatItDefinesLeavesTheFactorsUnanswered() {
        Map<String, List<String>> left =
                unansweredBelowTheInput(record("c == a * b") + BEHAVIOR);

        assertFalse(left.get("n.a").isEmpty());
        assertFalse(left.get("n.b").isEmpty());
    }

    /**
     * A step is worked out on the order its operands are on, not the order of what it becomes:
     * {@code a * b} is a product of whole numbers before {@code Decimal.fromInt} makes it a
     * decimal, and it aborts there whatever the decimal beside it could hold.
     */
    @Test
    void aProductOfWholeNumbersMadeADecimalAfterwardsLeavesTheFactorsUnanswered() {
        Map<String, List<String>> left = unansweredBelowTheInput("""
                module demo

                data N = { a: Int, b: Int, c: Decimal }
                    invariant Decimal.compare(c, Decimal.fromInt(a * b)) == 0
                """ + BEHAVIOR);

        assertFalse(left.get("n.a").isEmpty(), "a of the greatest whole number has no b");
        assertFalse(left.get("n.b").isEmpty());
    }

    /**
     * A step answers the order of its own type, and not the order of what it was made of:
     * {@code Decimal.fromInt} takes a whole number and answers a decimal, so whole numbers made
     * decimals before they are multiplied are multiplied as decimals, which do not stop, and a
     * product past the width of a whole number is a value.
     */
    @Test
    void wholeNumbersMadeDecimalsBeforeTheyAreMultipliedLeaveTheFactorsFree() {
        assertEquals(Map.of("n.a", List.of(), "n.b", List.of(), "n.c", List.of()),
                unansweredBelowTheInput("""
                        module demo

                        data Large = Int
                            invariant value >= 4000000000 && value <= 5000000000

                        data N = { a: Large, b: Large, c: Decimal }
                            invariant Decimal.compare(c,
                                Decimal.fromInt(a.value) * Decimal.fromInt(b.value)) == 0
                        """ + BEHAVIOR));
    }

    /** Where the places lie well inside the width the arithmetic never leaves it. */
    @Test
    void aProductOfWholeNumbersThatStaysInsideTheirWidthLeavesTheFactorsFree() {
        assertEquals(Map.of("n.a", List.of(), "n.b", List.of(), "n.c", List.of()),
                unansweredBelowTheInput("""
                        module demo

                        data Small = Int
                            invariant value >= 0 && value <= 1000

                        data N = { a: Small, b: Small, c: Int }
                            invariant c == a.value * b.value
                        """ + BEHAVIOR));
    }

    /**
     * The places are free only where the number cannot come to what the defined place refuses.
     *
     * <p>{@code c == a * b} beside {@code c == 1} leaves no {@code a} of nought, so the rule that
     * defines {@code c} restricts both factors together with the one that holds it. Taken in because
     * the rule is a definition, the question stood answered while the pair was not free.
     */
    @Test
    void aDefinitionBesideARuleHoldingTheDefinedPlaceLeavesItsFactorsUnanswered() {
        Map<String, List<String>> left = unansweredBelowTheInput("""
                module demo

                data N = { a: Int, b: Int, c: Int }
                    invariant defined = c == a * b
                    invariant pinned = c == 1
                """ + BEHAVIOR);

        assertFalse(left.get("n.a").isEmpty(), "a of nought has no b to make c one");
        assertFalse(left.get("n.b").isEmpty());
    }

    /**
     * A range is a box, and a rule that ties the defined place to another position puts no end on
     * it that shows the tie: {@code c == a + 1} beside {@code c == a * b} leaves only the pairs of
     * {@code a} and {@code b} with {@code a * (b - 1) == 1}, and says nothing in c's range.
     */
    @Test
    void aDefinitionBesideARuleTyingTheDefinedPlaceToAnotherLeavesItsFactorsUnanswered() {
        Map<String, List<String>> left = unansweredBelowTheInput("""
                module demo

                data N = { a: Int, b: Int, c: Int }
                    invariant defined = c == a * b
                    invariant tied = c == a + 1
                """ + BEHAVIOR);

        assertFalse(left.get("n.a").isEmpty(), "a of nought or one has no b to make c both");
        assertFalse(left.get("n.b").isEmpty());
    }

    /** And so is a factor that another rule ties to the other, whatever ranges they are left. */
    @Test
    void aDefinitionWhoseFactorsAreTiedToEachOtherLeavesThemUnanswered() {
        Map<String, List<String>> left = unansweredBelowTheInput("""
                module demo

                data Count = Int
                    invariant value >= 0

                data N = { a: Count, b: Count, c: Count }
                    invariant defined = c.value == a.value * b.value
                    invariant together = a.value + b.value <= 10
                """ + BEHAVIOR);

        assertFalse(left.get("n.a").isEmpty(), "a of ten leaves b of nought");
        assertFalse(left.get("n.b").isEmpty());
    }

    @Test
    void aDefinitionOfAPlaceThatAdmitsLessThanTheNumberCanComeToLeavesItsFactorsUnanswered() {
        Map<String, List<String>> left = unansweredBelowTheInput("""
                module demo

                data Small = Int
                    invariant value >= 0 && value <= 10

                data N = { a: Int, b: Int, c: Small }
                    invariant c.value == a * b
                """ + BEHAVIOR);

        assertFalse(left.get("n.a").isEmpty(), "a product past ten has no c beside it");
        assertFalse(left.get("n.b").isEmpty());
    }

    /**
     * A range is the hull of what a place admits, and a place that admits two numbers inside it
     * admits less than the range: {@code c} of one or three has no {@code a} of two beside a
     * {@code b} of one.
     */
    @Test
    void aDefinitionOfAPlaceThatAdmitsASetInsideItsRangeLeavesItsFactorsUnanswered() {
        Map<String, List<String>> left = unansweredBelowTheInput("""
                module demo

                data Restricted = Int
                    invariant value == 1 || value == 3

                data N = { a: Int, b: Int, c: Restricted }
                    invariant lower = a >= 1 && a <= 3
                    invariant one = b == 1
                    invariant product = c.value == a * b
                """ + BEHAVIOR);

        assertFalse(left.get("n.a").isEmpty(), "a of two has no c beside it");
    }

    /**
     * Whole numbers stop at a width, and a product past it is no value of any place: the arithmetic
     * aborts. A factor of the greatest whole number has no second factor of two or more.
     */
    @Test
    void aProductOfWholeNumbersThatCanLeaveTheirWidthLeavesItsFactorsUnanswered() {
        Map<String, List<String>> left = unansweredBelowTheInput("""
                module demo

                data Positive = Int
                    invariant value >= 2

                data N = { a: Positive, b: Positive, c: Int }
                    invariant c == a.value * b.value
                """ + BEHAVIOR);

        assertFalse(left.get("n.a").isEmpty(), "a of the greatest whole number has no b");
        assertFalse(left.get("n.b").isEmpty());
    }

    @Test
    void aDefinitionOfAPlaceThatAdmitsEverythingTheNumberCanComeToLeavesItsFactorsFree() {
        assertEquals(Map.of("n.a", List.of(), "n.b", List.of(), "n.c", List.of()),
                unansweredBelowTheInput("""
                        module demo

                        data Count = Decimal
                            invariant value >= 0.0m

                        data N = { a: Count, b: Count, c: Count }
                            invariant c.value == a.value * b.value
                        """ + BEHAVIOR));
    }

    /**
     * A number that is made of a place that another number defines is known once that one is.
     *
     * <p>{@code d == c * b} with {@code c == a * b}: settling {@code a} and {@code b} settles
     * {@code c}, and only then are the places {@code d} is made of at numbers.
     */
    @Test
    void aNumberMadeOfADefinedPlaceStandsAtWhatItComesToOnceThatPlaceDoes() {
        FieldDomains read = fieldsOf("""
                module demo

                data N = { a: Int, b: Int, c: Int, d: Int }
                    invariant c == a * b
                    invariant d == c * b
                """);
        Map<RuleKey, Count> fixed = new LinkedHashMap<>();
        fixed.put(RuleKey.of("a"), new Count(new BigDecimal(3)));
        fixed.put(RuleKey.of("b"), new Count(new BigDecimal(4)));

        FieldDomains.Composing composing = read.composing(FieldDomains.atValues(fixed));

        assertEquals(0, new BigDecimal(12).compareTo(pointOf(composing.at(RuleKey.of("c")).values())));
        assertEquals(0, new BigDecimal(48).compareTo(pointOf(composing.at(RuleKey.of("d")).values())));
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
