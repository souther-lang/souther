package souther.compiler;

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ComposedRows;
import souther.compiler.query.ItemAssessment;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a walk makes of each element by multiplying its fields and rounding what it made is read as
 * the number it is, two totals of one list of decimals are read as the one total they come to, and
 * the rows written for it come to what they were written for.
 *
 * <p>The model is a blended discount cap: what each line comes to after its discount, rounded to
 * cents, is at least six tenths of what the lines come to before it. Held by working each row out
 * here with {@link BigDecimal}, rounding half up at two places as {@code Decimal.round} does: a row
 * at a point of the line comes to the number its label names, and a row composed for a rule is run
 * through the module and answers what the cap works out to.
 */
class AProductOrARoundingOfEachElementIsReadAsTheTotalItComesToTest {

    private static final String LINES = """
            module p

            data Line = { qty: Int, price: Decimal, discount: Decimal }

            behavior capped : (xs: List<Line>) -> Int

            let net (x: Line): Decimal =
                Decimal.round(2, HALF_UP, Decimal.fromInt(x.qty) * x.price * (1.0m - x.discount))

            let gross (x: Line): Decimal =
                Decimal.round(2, HALF_UP, Decimal.fromInt(x.qty) * x.price)

            let capped (xs) = %s
            """;

    /** As the cap is written in the model it comes from. */
    private static final String AS_WRITTEN = cap("""
            if Decimal.compare(List.sum(List.map(x -> net(x), xs)),
                               List.sum(List.map(x -> gross(x), xs)) * 0.6m) >= 0 then 1 else 0""");

    /** The discount multiplied out, and the closures written in place. */
    private static final String MULTIPLIED_OUT = cap("""
            if Decimal.compare(List.sum(List.map(x -> Decimal.round(2, HALF_UP,
                                   Decimal.fromInt(x.qty) * x.price
                                       - Decimal.fromInt(x.qty) * x.price * x.discount), xs)),
                               List.sum(List.map(x -> gross(x), xs)) * 0.6m) >= 0
            then 1 else 0""");

    /** What is left after the discount written first, so a factor with a constant in it is
     *  multiplied by fields. */
    private static final String DISCOUNT_FIRST = cap("""
            if Decimal.compare(List.sum(List.map(x -> Decimal.round(2, HALF_UP,
                                   (1.0m - x.discount) * Decimal.fromInt(x.qty) * x.price), xs)),
                               List.sum(List.map(x -> gross(x), xs)) * 0.6m) >= 0
            then 1 else 0""");

    /** The two sides the other way round. */
    private static final String TURNED = cap("""
            if Decimal.compare(List.sum(List.map(x -> gross(x), xs)) * 0.6m,
                               List.sum(List.map(x -> net(x), xs))) <= 0 then 1 else 0""");

    /** Each total behind a name. */
    private static final String NAMED = cap("""
            {
                let after = List.sum(List.map(x -> net(x), xs))
                let before = List.sum(List.map(x -> gross(x), xs))
                if Decimal.compare(after, before * 0.6m) >= 0 then 1 else 0
            }""");

    /** Another weight, which is another rule. */
    private static final String HALF = cap("""
            if Decimal.compare(List.sum(List.map(x -> net(x), xs)),
                               List.sum(List.map(x -> gross(x), xs)) * 0.5m) >= 0 then 1 else 0""");

    private static String cap(String body) {
        return LINES.formatted(body.replace("\n", "\n    "));
    }

    private static final Pattern TOTAL = Pattern.compile("List\\.sum\\(\\{[^|]*\\| xs\\[\\*\\]\\}\\)");

    /** The one total each spelling of the cap is read as, and that it is read whole. */
    private static Set<String> totalsOf(String model) {
        String report = report(measured(model));
        assertFalse(report.contains("not read:"), report);
        Set<String> totals = new LinkedHashSet<>();
        Matcher found = TOTAL.matcher(report);
        while (found.find()) {
            totals.add(found.group());
        }
        return totals;
    }

    /**
     * However the cap is written — the discount multiplied out, the sides turned round, each total
     * behind a name — it is one total of what each line comes to, and the products and the
     * roundings are in it. Another weight is another total.
     */
    @Test
    void everySpellingOfTheCapIsTheOneTotal() {
        Set<String> asWritten = totalsOf(AS_WRITTEN);
        assertEquals(1, asWritten.size(), () -> "one total: " + asWritten);
        String total = asWritten.iterator().next();
        assertTrue(total.contains("round(2, HALF_UP, ") && total.contains("price·qty"), total);
        for (String other : List.of(MULTIPLIED_OUT, DISCOUNT_FIRST, TURNED, NAMED)) {
            assertEquals(asWritten, totalsOf(other), other);
        }
        assertFalse(totalsOf(HALF).equals(asWritten), "half is another rule");
    }

    /** What the lines of a row come to after the cap's rounding, less {@code weight} of what they
     *  come to before it. */
    private static BigDecimal capOf(String row, BigDecimal weight) {
        BigDecimal after = BigDecimal.ZERO;
        BigDecimal before = BigDecimal.ZERO;
        Matcher line = LINE.matcher(row);
        while (line.find()) {
            BigDecimal qty = new BigDecimal(line.group(1));
            BigDecimal price = new BigDecimal(line.group(2));
            BigDecimal discount = new BigDecimal(line.group(3));
            after = after.add(qty.multiply(price).multiply(BigDecimal.ONE.subtract(discount))
                    .setScale(2, RoundingMode.HALF_UP));
            before = before.add(qty.multiply(price).setScale(2, RoundingMode.HALF_UP));
        }
        return after.subtract(weight.multiply(before));
    }

    private static final Pattern LINE = Pattern.compile(
            "Line \\{ qty = (-?\\d+), price = (-?[\\d.]+)m, discount = (-?[\\d.]+)m \\}");

    private static final Pattern EQUAL = Pattern.compile("^[^<]* = 0$");
    private static final Pattern ABOVE = Pattern.compile("^0 < ");
    private static final Pattern BELOW = Pattern.compile(" < 0$");

    /**
     * Every row at a point of the cap's line, for every spelling and both weights, comes to the
     * number its label names: on the line, above it, or below it, worked out here line by line.
     */
    @Test
    void aRowAtAPointComesToWhatItsLabelNames() {
        int checked = 0;
        for (Map.Entry<String, BigDecimal> each : Map.of(AS_WRITTEN, new BigDecimal("0.6"),
                MULTIPLIED_OUT, new BigDecimal("0.6"), DISCOUNT_FIRST, new BigDecimal("0.6"),
                TURNED, new BigDecimal("0.6"), NAMED, new BigDecimal("0.6"),
                HALF, new BigDecimal("0.5")).entrySet()) {
            Compilation compilation = measured(each.getKey());
            for (BorderAssessment border : Adequacy.readingsOf(compilation.db(), "p")
                    .get("capped")) {
                for (ItemAssessment item : border.items().values()) {
                    if (!(item instanceof ItemAssessment.Owed owed)) {
                        continue;
                    }
                    for (ItemAssessment.Attempt attempt : owed.searches().each()) {
                        if (!(attempt instanceof ItemAssessment.Attempt.Certified certified)) {
                            continue;
                        }
                        String row = certified.row().inputs().getFirst().text();
                        BigDecimal worked = capOf(row, each.getValue());
                        for (var purpose : certified.row().purposes()) {
                            for (String label : purpose.labels()) {
                                checked += agrees(label, row, worked);
                            }
                        }
                    }
                }
            }
        }
        assertTrue(checked >= 10, "a row at each point of each spelling: " + checked);
    }

    /** One where {@code label} names a point {@code worked} is at, which it must be; nought where
     *  it names no point of the line. The label's number is the line's, which is the cap's
     *  difference weighed by what its terms share — nought on either side is nought. */
    private static int agrees(String label, String row, BigDecimal worked) {
        if (!label.contains("List.sum(")) {
            return 0;
        }
        Matcher equal = EQUAL.matcher(label);
        if (equal.find()) {
            assertEquals(0, worked.signum(), () -> label + " at " + row + " comes to " + worked);
            return 1;
        }
        boolean above = ABOVE.matcher(label).find();
        boolean below = BELOW.matcher(label).find();
        assertTrue(above || below, label);
        assertEquals(above ? 1 : -1, worked.signum(),
                () -> label + " at " + row + " comes to " + worked);
        return 1;
    }

    /**
     * A row composed for each way the cap comes out is run through the module, and answers what
     * the cap works out to over its lines here.
     */
    @Test
    void everyRuleIsComposedARowThatTakesIt() {
        Compilation compilation = measured(AS_WRITTEN);
        List<String> texts = new ArrayList<>();
        Set<Integer> answers = new TreeSet<>();
        for (List<FixtureTemplate> row : composedForTheRules(compilation)) {
            String text = row.getFirst().text();
            int answer = capOf(text, new BigDecimal("0.6")).signum() >= 0 ? 1 : 0;
            texts.add(text);
            answers.add(answer);
            assertEquals(new AnswerObservation.Answered(new ObservedValue.Integer(answer)),
                    ComposedRows.answer(compilation, "capped", row),
                    () -> text + " is answered as its lines say");
        }
        assertEquals(Set.of(0, 1), answers, () -> "a row on each side, and not " + texts);
    }

    /**
     * A row a model writes is read at what its roundings come to. A line of one item at
     * {@code 1.006} with four tenths off is sixty cents after the discount and a hundred and one
     * before it, so its six tenths are past what is left: the row is below the line. Without the
     * rounding the two are equal, and the row would stand on it.
     */
    @Test
    void aRowIsReadAtWhatItsRoundingsComeTo() {
        String model = AS_WRITTEN + """

                example capped
                    | "off the steps" : ([Line { qty = 1, price = 1.006m, discount = 0.4m }]) -> 0
                """;
        BigDecimal worked = capOf("Line { qty = 1, price = 1.006m, discount = 0.4m }",
                new BigDecimal("0.6"));
        assertEquals(-1, worked.signum(), "worked out here: " + worked);
        String report = report(measured(model));
        assertTrue(report.contains("! no row is at the ON point"), report);
        assertFalse(report.contains("! no row is at the OUT point"), report);
    }

    /**
     * Totals of whole numbers are left as they were written: a sum of them stops at the end of a
     * long, and two writings of one total stop at different totals. Of decimals, which have no end
     * to pass, the same two totals are the one total.
     */
    @Test
    void totalsOfWholeNumbersAreLeftAsTheyWereWritten() {
        String rule = """
                module w
                data Line = { a: %s, b: %s }
                behavior f : (xs: List<Line>) -> Int
                let f (xs) =
                    if %s then 1 else 0
                """;
        String whole = report(measured(rule.formatted("Int", "Int",
                "List.sum(List.map(x -> x.a, xs)) + List.sum(List.map(x -> x.a + x.b, xs)) > 0")));
        assertTrue(whole.contains("List.sum(xs[*].a)"), whole);
        assertTrue(whole.contains("List.sum({1·a + 1·b + 0 | xs[*]})"), whole);
        String decimal = report(measured(rule.formatted("Decimal", "Decimal",
                "Decimal.compare(List.sum(List.map(x -> x.a, xs))"
                        + " + List.sum(List.map(x -> x.a + x.b, xs)), 0.0m) > 0")));
        assertTrue(decimal.contains("List.sum({2·a + 1·b + 0 | xs[*]})"), decimal);
        assertFalse(decimal.contains("List.sum(xs[*].a)"), decimal);
    }

    private static final String HELD_STILL = """
            module h
            data Q = Int
                invariant value >= 2 && value <= 3
            data Line = { q: Q, p: %s }
            behavior f : (xs: List<Line>) -> Int
            let f (xs) =
                if List.sum(List.map(x -> x.q.value * %s, xs)) >= %d then 1 else 0
            """;

    /**
     * A field held still while the other is solved for is written as a value of its position,
     * under the name its declaration puts there, at a value the declaration leaves it: one is
     * outside what a {@code Q} holds, so the field is held at two.
     */
    @Test
    void aFieldHeldStillIsAValueOfItsPosition() {
        String rows = rowsOf(measured(HELD_STILL.formatted("Int", "x.p", 8)));
        assertTrue(rows.contains("Line { q = Q(2), p = 4 }"), rows);
        assertFalse(rows.contains("no row for"), rows);
    }

    /**
     * Held at one value in every element, both fields of a product of two values that are two or
     * three come to even totals only, and nine — three times three — is a total such a list comes
     * to all the same. So the point beside the line at ten is said as one the search walked some
     * of the containers for, and not as one no container comes to.
     */
    @Test
    void aPointTheFieldsHeldStillDoNotReachIsNoPointNothingReaches() {
        String model = HELD_STILL.replace("data Line", "data P = Int\n    invariant value >= 2"
                + " && value <= 3\ndata Line").formatted("P", "x.p.value", 10);
        String report = report(measured(model));
        assertTrue(report.contains("List.sum({1·p·q + 0 | xs[*]}): = 9 — "), report);
        String nine = report.lines().filter(line -> line.contains(": = 9 — ")).findFirst()
                .orElseThrow();
        assertTrue(nine.contains("the containers whose elements differ at a field the computed"
                + " number reads besides the one solved for"), nine);
        assertFalse(nine.contains("no value can stand there"), nine);
    }

    private static List<List<FixtureTemplate>> composedForTheRules(Compilation compilation) {
        List<List<FixtureTemplate>> out = new ArrayList<>();
        Adequacy.generatedOf(compilation.db(), compilation.modules().get(0)).get("capped")
                .generation().stream()
                .filter(each -> each.finding().about() instanceof About.ARuleNoRowTakes)
                .forEach(each -> {
                    if (each.outcome() instanceof GenerationOutcome.Generated made) {
                        made.candidates().forEach(row -> out.add(row.inputs()));
                    }
                });
        return out;
    }

    private static String rowsOf(Compilation compilation) {
        return GeneratedRows.of(compilation, null, null,
                SourceRendering.namedByIdentity(SourceLayouts.NONE)).text();
    }

    /** Each model measured once for the class: the methods read the same models, and only read
     *  them. */
    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

    private static Compilation measured(String source) {
        return MEASURED.computeIfAbsent(source, text -> {
            Compilation compilation = Compilation.ofSource(text, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            return compilation;
        });
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
