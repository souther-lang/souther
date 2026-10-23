package souther.compiler.partition;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Arithmetic no form says is reported as the arithmetic it was, at the positions it is about,
 * whichever way the comparison reaches them: compared directly, handed to an operation over a
 * container, counted, named, written in a helper, under an operation whose form the library states,
 * or written in an invariant.
 *
 * <p>The arithmetic decides which operation it met, where it composes the operands. What a report
 * says is that decision carried through, so a closure or a call around the product changes nothing
 * about it, and nothing is asked of where the value came from to say it again. Held as the pairs of
 * a position and a word, so a reason that reaches one of the two positions a product names and not
 * the other is a failure.
 *
 * <p>The products here weigh a factor by two before they are taken, which is a product the
 * arithmetic does not read: {@code 2 * q} passes where its type stops for half the values of
 * {@code q}, whatever the other factor is. A product of two numbers each read as itself is read,
 * and whatever carries it leaves no place of it unread — the last of these.
 */
class AProductOfTwoInputsIsReportedAsAProductWhateverCarriesItTest {

    private static final String DATA = """
            module demo

            data A = { q: Int, p: Int }
            """;

    @Test
    void aProductInAnyIsAProductAtBothFields() {
        assertEquals(List.of("xs[*].p: NON_AFFINE_PRODUCT", "xs[*].q: NON_AFFINE_PRODUCT"),
                reasons("""
                        behavior f : (xs: List<A>) -> Bool
                        let f (xs) = List.any(i -> 2 * i.q * i.p >= 1000, xs)
                        """));
    }

    @Test
    void theSameProductCountedIsTheSameProduct() {
        assertEquals(List.of("xs: NON_AFFINE_PRODUCT", "xs[*].p: NON_AFFINE_PRODUCT",
                        "xs[*].q: NON_AFFINE_PRODUCT"),
                reasons("""
                        behavior f : (xs: List<A>) -> Bool
                        let f (xs) = List.length(List.filter(i -> 2 * i.q * i.p >= 1000, xs)) >= 1
                        """));
    }

    @Test
    void aProductNamedBeforeItIsComparedIsTheSameProduct() {
        assertEquals(List.of("xs[*].p: NON_AFFINE_PRODUCT", "xs[*].q: NON_AFFINE_PRODUCT"),
                reasons("""
                        behavior f : (xs: List<A>) -> Bool
                        let f (xs) = List.any(i -> {
                            let amount = 2 * i.q * i.p
                            amount >= 1000
                        }, xs)
                        """));
    }

    @Test
    void aProductWrittenInAHelperIsTheSameProduct() {
        assertEquals(List.of("xs: NON_AFFINE_PRODUCT", "xs[*]: NON_AFFINE_PRODUCT"),
                reasons("""
                        behavior amount : (a: A) -> Int
                        let amount (a) = 2 * a.q * a.p

                        behavior f : (xs: List<A>) -> Bool
                        let f (xs) = List.length(List.filter(i -> amount(i) >= 1000, xs)) >= 1
                        """));
    }

    /**
     * An operation whose form the library states, handed a product. The reading stops at the call,
     * which is what the author wrote, and it stopped for what stopped its argument.
     */
    @Test
    void aProductUnderAnOperationWhoseFormIsStatedIsTheSameProduct() {
        assertEquals(List.of("a: NON_AFFINE_PRODUCT", "b: NON_AFFINE_PRODUCT"),
                reasons("""
                        behavior f : (a: Int, b: Int) -> Bool
                        let f (a, b) = Int.add(2 * a * b, 1) >= 1000
                        """));
    }

    /**
     * A quotient by an input held against another value is no line, and says it is a divisor.
     * Against a number it is a line on each sign of the divisor, which stops where the comparison
     * written out over the product on each sign stops: what is left unread of it is the relation,
     * and not the division. The sign is what the quotient knows of the divisor and a product
     * written alone does not: held above nought, the divisor keeps the dividend's least values
     * below the line. A comparison read to the end is not asked here: the quotient parts its
     * divisor at the sign itself, and the arms written out leave that to the conditions before
     * them.
     */
    @Test
    void aQuotientByAnInputIsADivisorAndNotAProduct() {
        assertEquals(List.of("xs[*].p: NON_CONSTANT_DIVISOR", "xs[*].q: NON_CONSTANT_DIVISOR"),
                reasons("""
                        behavior f : (xs: List<A>) -> Bool
                        let f (xs) = List.any(i -> i.q / i.p >= i.q, xs)
                        """));
        assertEquals(stopped("""
                        behavior f : (xs: List<A>) -> Bool
                        let f (xs) = List.any(i -> if i.p > 0 then i.q >= 10 * i.p
                            else if i.p < 0 then i.q <= 10 * i.p else false, xs)
                        """),
                stopped("""
                        behavior f : (xs: List<A>) -> Bool
                        let f (xs) = List.any(i -> i.q / i.p >= 10, xs)
                        """));
    }

    /**
     * Two parts of one statement that stopped for different arithmetic are not one operation, and
     * the count over them does not name either: what they have in common is a part not read. Each
     * conjunct is a comparison of its own at the element, and says what it met.
     */
    @Test
    void twoDifferentOperationsAreNeitherOfThemWhereTheyAreCountedTogether() {
        assertEquals(List.of("xs: RULE_MEANING_NOT_READ",
                        "xs[*].p: NON_AFFINE_PRODUCT", "xs[*].p: NON_CONSTANT_DIVISOR",
                        "xs[*].p: RULE_MEANING_NOT_READ",
                        "xs[*].q: NON_AFFINE_PRODUCT", "xs[*].q: NON_CONSTANT_DIVISOR",
                        "xs[*].q: RULE_MEANING_NOT_READ"),
                reasons("""
                        behavior f : (xs: List<A>) -> Bool
                        let f (xs) = List.length(List.filter(
                            i -> 2 * i.q * i.p >= 1000 && i.q / i.p >= i.q, xs)) >= 1
                        """));
        // A quotient against a number counted beside the product is read, and leaves what the
        // comparison written out over the product leaves.
        assertEquals(reasons("""
                        behavior f : (xs: List<A>) -> Bool
                        let f (xs) = List.length(List.filter(
                            i -> 2 * i.q * i.p >= 1000 && i.q >= 10 * i.p, xs)) >= 1
                        """),
                reasons("""
                        behavior f : (xs: List<A>) -> Bool
                        let f (xs) = List.length(List.filter(
                            i -> 2 * i.q * i.p >= 1000 && i.q / i.p >= 10, xs)) >= 1
                        """));
    }

    @Test
    void aProductBySomethingConstantIsNotOneAtAll() {
        assertFalse(reasons("""
                behavior f : (xs: List<A>) -> Bool
                let f (xs) = List.any(i -> i.q * 2 >= 1000, xs)
                """).toString().contains("NON_AFFINE_PRODUCT"));
        assertFalse(reasons("""
                behavior f : (xs: List<A>) -> Bool
                let f (xs) = List.any(i -> i.q + i.p >= 1000, xs)
                """).toString().contains("NON_AFFINE_PRODUCT"));
    }

    /** A product with arithmetic before or after it, which the run does in the type and a form
     *  does not hold, is a product at each of its positions, as one nothing reads is. */
    @Test
    void aProductBetweenTwoPositionsIsAProductAtEach() {
        for (String condition : List.of("2 * a * b >= 1000", "Int.add(a * b, 1) >= 1000")) {
            assertEquals(List.of("a: NON_AFFINE_PRODUCT", "b: NON_AFFINE_PRODUCT"),
                    reasons("""
                            behavior f : (a: Int, b: Int) -> Bool
                            let f (a, b) = %s
                            """.formatted(condition)), condition);
        }
    }

    /**
     * A product of two numbers each read as itself is read as one, and no carrier leaves a place
     * of it unread: compared directly, handed to an operation over a container, counted, named, or
     * written in a helper.
     */
    @Test
    void aProductTheArithmeticReadsLeavesNoPlaceUnreadWhateverCarriesIt() {
        for (String behaviors : List.of("""
                        behavior f : (a: Int, b: Int) -> Bool
                        let f (a, b) = a * b >= 1000
                        """, """
                        behavior f : (xs: List<A>) -> Bool
                        let f (xs) = List.any(i -> i.q * i.p >= 1000, xs)
                        """, """
                        behavior f : (xs: List<A>) -> Bool
                        let f (xs) = List.length(List.filter(i -> i.q * i.p >= 1000, xs)) >= 1
                        """, """
                        behavior f : (xs: List<A>) -> Bool
                        let f (xs) = List.any(i -> {
                            let amount = i.q * i.p
                            amount >= 1000
                        }, xs)
                        """, """
                        behavior amount : (a: A) -> Int
                        let amount (a) = a.q * a.p

                        behavior f : (xs: List<A>) -> Bool
                        let f (xs) = List.length(List.filter(i -> amount(i) >= 1000, xs)) >= 1
                        """)) {
            assertEquals(List.of(), reasons(behaviors), behaviors);
        }
    }

    /** A product in a clause, which is read by the invariant's reader and not a body's, and that
     *  reader takes no product of two numbers as one. */
    @Test
    void aProductInAnInvariantIsAProduct() {
        String model = """
                module demo

                data Box = { w: Int, h: Int }
                    invariant w * h <= 100

                behavior f : (b: Box) -> Bool
                let f (b) = true
                """;
        assertEquals(List.of("b.h: NON_AFFINE_PRODUCT", "b.w: NON_AFFINE_PRODUCT"),
                reasonsOf(model));
    }

    /**
     * A product in a clause under an operation the library states no form of is the product it is
     * in what a report tells the author, and the operation around it takes nothing of the reason.
     */
    @Test
    void aProductInAnInvariantUnderAnOperationWithNoStatedFormIsTheSameProduct() {
        List<String> bare = accountedFor("net.value == price.value * disc.value");
        assertTrue(bare.getFirst().contains("a product of two values that are not constants"),
                bare.toString());
        for (String clause : List.of("Decimal.compare(net.value, price.value * disc.value) == 0",
                "Decimal.round(2, HALF_UP, price.value * disc.value) == net.value")) {
            assertEquals(bare, accountedFor(clause), clause);
        }
    }

    /** What the report says is not accounted for, one line to a place. */
    private static List<String> accountedFor(String clause) {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Price = Decimal
                    invariant value >= 0.0m
                data Disc = Decimal
                    invariant value >= 0.0m && value <= 0.5m
                data Money = Decimal
                    invariant value >= 0.0m
                data Line = { qty: Int, price: Price, disc: Disc, net: Money }
                    invariant %s

                behavior pick : (l: Line) -> Int
                let pick (l) = if l.qty > 3 then 1 else 0
                """.formatted(clause), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .filter(line -> line.contains("not accounted for"))
                .map(String::strip)
                .sorted()
                .toList();
    }

    /** Each position paired with the word a report is told, in a steady order. */
    private static List<String> reasons(String behaviors) {
        return reasonsOf(DATA + "\n" + behaviors);
    }

    /** The same, of the readings that stopped alone, and not of a rule read to the end. */
    private static List<String> stopped(String behaviors) {
        return notReadIn(DATA + "\n" + behaviors).stream()
                .filter(PartitionEvidence.NotRead::readingStopped)
                .map(each -> each.at() + ": " + each.reason())
                .distinct()
                .sorted()
                .collect(Collectors.toList());
    }

    private static List<PartitionEvidence.NotRead> notReadIn(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, () -> "the model under test compiles: " + model);
        PartitionEvidence measured = coverage.get("f");
        assertNotNull(measured, () -> "f was measured: " + model);
        return measured.notRead();
    }

    private static List<String> reasonsOf(String model) {
        return notReadIn(model).stream()
                .map(each -> each.at() + ": " + each.reason())
                .distinct()
                .sorted()
                .collect(Collectors.toList());
    }
}
