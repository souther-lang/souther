package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Place;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.PartitionEvidence;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What two whole numbers of the input come to multiplied is a number of its own, and a rule about
 * it is a line on that number and on neither factor.
 *
 * <p>{@code price * quantity >= 1000} relates the two: fixing either leaves a line on the other at
 * the level over it, which moves with the value fixed. A row at the line is a pair whose product is
 * the level. And a factor's own values divide the rule where they settle it whatever the other is:
 * at nought the product is nought, so nought is a class of each factor, and every other value
 * leaves the other reaching both sides of the level over it.
 */
class AProductOfTwoNumbersIsALineOnTheProductTest {

    private static final String PRICE_AND_QUANTITY = "price: Int, quantity: Int";

    /** The line is on the product, and nought is a class of each factor. */
    @Test
    void aProductIsALineOnTheProductAndNoughtIsAClassOfEachFactor() {
        Compilation compilation = compiled("", PRICE_AND_QUANTITY, "price * quantity >= 1000");
        assertEquals(List.of("1000"), bordersOf(linesOf(compilation)));
        Map<String, List<String>> classes = classesOf(measured(compilation));
        assertEquals(List.of("price/= 0", "price//= 0"), classes.get("price"), classes.toString());
        assertEquals(List.of("quantity/= 0", "quantity//= 0"), classes.get("quantity"),
                classes.toString());
    }

    /** A row the line is owed is a pair whose product is the level the row is labelled with. */
    @Test
    void aRowAtTheLineIsAPairWhoseProductIsTheLevel() {
        List<String> labels = new ArrayList<>();
        for (Row row : certifiedRows(linesOf(compiled("", PRICE_AND_QUANTITY,
                "price * quantity >= 1000")))) {
            for (String label : row.labels()) {
                if (label.startsWith("price * quantity = ")) {
                    long level = Long.parseLong(label.substring(label.lastIndexOf(' ') + 1));
                    long price = Long.parseLong(row.inputs().get(0));
                    long quantity = Long.parseLong(row.inputs().get(1));
                    assertEquals(level, Math.multiplyExact(price, quantity),
                            label + " at " + row.inputs());
                    labels.add(label);
                }
            }
        }
        assertEquals(List.of("price * quantity = 1000", "price * quantity = 999"),
                labels.stream().sorted().toList(), "the line and the value below it");
    }

    /**
     * A level only one pair of the factors' values multiplies to is still reached, by the divisor
     * the walk tries: with the factors held at seven or more, 49 is only seven times seven.
     */
    @Test
    void aLevelIsReachedByThePairItsDivisorsMake() {
        String prelude = """
                data AtLeastSeven = Int
                    invariant value >= 7
                """;
        List<String> labels = new ArrayList<>();
        for (Row row : certifiedRows(linesOf(compiled(prelude, "a: AtLeastSeven, b: AtLeastSeven",
                "a.value * b.value == 49")))) {
            for (String label : row.labels()) {
                if (label.endsWith(" = 49")) {
                    assertEquals(List.of("AtLeastSeven(7)", "AtLeastSeven(7)"), row.inputs(),
                            label);
                    labels.add(label);
                }
            }
        }
        assertEquals(List.of("a * b = 49"), labels);
    }

    /**
     * One product however it is written: factors either way round, the comparison either way
     * round, or behind a name. The line is at one level and the classes are one partition.
     */
    @Test
    void aProductIsOneLineHoweverItIsWritten() {
        Map<List<String>, String> spellings = new LinkedHashMap<>();
        spellings.put(List.of("guard price * quantity >= 1000 else No", "Ok"), "written");
        spellings.put(List.of("guard quantity * price >= 1000 else No", "Ok"), "turned round");
        spellings.put(List.of("guard 1000 <= price * quantity else No", "Ok"), "faced the other way");
        spellings.put(List.of("let amount = price * quantity", "guard amount >= 1000 else No", "Ok"),
                "named");
        List<String> borders = null;
        Map<String, List<String>> classes = null;
        for (Map.Entry<List<String>, String> each : spellings.entrySet()) {
            Compilation compilation = compiled("", PRICE_AND_QUANTITY, each.getKey(), "");
            List<String> theseBorders = bordersOf(linesOf(compilation));
            Map<String, List<String>> theseClasses = classesOf(measured(compilation));
            if (borders == null) {
                borders = theseBorders;
                classes = theseClasses;
            }
            assertEquals(borders, theseBorders, each.getValue());
            assertEquals(classes, theseClasses, each.getValue());
        }
    }

    /**
     * Factors held from one to a hundred thousand: from a thousand on, either one holds the rule
     * whatever the other is, so a thousand is where each factor's values part, and below it the
     * other reaches both sides of the level over it.
     */
    @Test
    void aFactorFarFromNoughtSettlesTheRuleAndIsAClassOfItsOwn() {
        String prelude = """
                data Price = Int
                    invariant value >= 1 && value <= 100000

                data Quantity = Int
                    invariant value >= 1 && value <= 100000
                """;
        Map<String, List<String>> classes = classesOf(measured(compiled(prelude,
                "price: Price, quantity: Quantity", "price.value * quantity.value >= 1000")));
        assertEquals(List.of("price/1 <= x < 1000", "price/1000 <= x <= 100000"),
                classes.get("price"), classes.toString());
        assertEquals(List.of("quantity/1 <= x < 1000", "quantity/1000 <= x <= 100000"),
                classes.get("quantity"), classes.toString());
    }

    /**
     * A product of one number with itself or of three numbers is not read as one, and neither is
     * a product with arithmetic before or after it, which the run does in the type: at
     * {@code price} of two to the sixty-second, {@code price * quantity * 2} stops the run for
     * every {@code quantity} above nought, where a product held against five hundred would come
     * out true. A factor weighed, negated or moved, and a product weighed, moved or negated, are
     * each named as the arithmetic was before.
     */
    @Test
    void aProductThisDoesNotReadIsNamedAsAProduct() {
        for (String condition : List.of("price * price >= 1000",
                "price * quantity * price >= 1000", "2 * price * quantity >= 1000",
                "(0 - price) * quantity >= 1000", "(price + 1) * quantity >= 1000",
                "price * quantity * 2 >= 1000", "price * quantity - 5 >= 995",
                "0 - price * quantity <= 0 - 1000")) {
            Compilation compilation = compiled("", PRICE_AND_QUANTITY, condition);
            assertEquals(List.of(), bordersOf(linesOf(compilation)), condition);
            assertEquals(List.of(UndividedPosition.Reason.NON_AFFINE_PRODUCT),
                    reasonsOf(measured(compilation)), condition);
        }
    }

    /**
     * Factors a rule of the value they sit in relates are tied, and what one reaches beside the
     * other is not shown: the line is drawn, and neither factor is divided or shown undivided.
     * The rule relating them is a relation of its own, and says so.
     */
    @Test
    void factorsARuleRelatesAreShownNothingOf() {
        String prelude = """
                data Pair = { a: Int, b: Int }
                    invariant a <= b
                """;
        Compilation compilation = compiled(prelude, "p: Pair", "p.a * p.b >= 1000");
        assertEquals(List.of("1000"), bordersOf(linesOf(compilation)));
        PartitionEvidence measured = measured(compilation);
        assertEquals(List.of(UndividedPosition.Reason.RULE_RELATING_TWO_VALUES,
                        UndividedPosition.Reason.RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE),
                reasonsOf(measured));
        assertEquals(Map.of(), classesOf(measured), "neither factor is divided");
    }

    /**
     * A product an invariant states is one the reading of its ends does not read, and that
     * reading tells each factor so. A line drawn on the product beside that would say of one
     * comparison that it was read and that it was not, so the invariant draws none and stays a rule
     * nothing read — weighed after the product or not. The same rule in a body is read, draws its
     * line, and makes nought a class of each factor.
     */
    @Test
    void anInvariantOverAProductDrawsNoLineAndStaysUnread() {
        for (String rule : List.of("rate * cap >= 10", "rate * cap * 2 >= 10")) {
            String declared = """
                    data Policy = { rate: Int, cap: Int }
                        invariant %s
                    """.formatted(rule);
            Compilation compilation = compiled(declared, "p: Policy", List.of("Ok"), "");
            assertEquals(List.of(), bordersOf(linesOf(compilation)), rule);
            PartitionEvidence measured = measured(compilation);
            assertTrue(reasonsOf(measured).contains(UndividedPosition.Reason.NON_AFFINE_PRODUCT),
                    rule + ": " + reasonsOf(measured));
            Map<String, List<String>> classes = classesOf(measured);
            assertTrue(!classes.containsKey("p.rate") && !classes.containsKey("p.cap"),
                    rule + ": " + classes);
        }

        String plain = "data Policy = { rate: Int, cap: Int }";
        Compilation guard = compiled(plain, "p: Policy", "p.rate * p.cap >= 10");
        assertEquals(List.of("10"), bordersOf(linesOf(guard)));
        Map<String, List<String>> guarded = classesOf(measured(guard));
        assertEquals(List.of("p.rate/= 0", "p.rate//= 0"), guarded.get("p.rate"),
                guarded.toString());
    }

    /**
     * Whether a clause draws a line is asked of that clause: the end {@code rate >= 0} places
     * beside an unread product is still drawn, and a sum and a length an invariant relates to a
     * field, which the reading of ends reads, still draw theirs. So do the days between two dates
     * and a comparison of two decimals, which the reading of ends has no atom for and names no
     * operation of: what it tells their places says nothing a line contradicts.
     */
    @Test
    void anUnreadClauseTakesNoOtherClausesLineWithIt() {
        Compilation beside = compiled("""
                data Policy = { rate: Int, cap: Int }
                    invariant rate >= 0 && rate * cap >= 10
                """, "p: Policy", List.of("Ok"), "");
        List<BorderAssessment> lines = linesOf(beside);
        assertEquals(List.of(), bordersOf(lines));
        assertTrue(lines.stream().anyMatch(each -> each.axis().equals("f/p.rate")
                && each.value().equals("0")), describe(lines));

        for (String[] related : List.of(new String[] {"a: Int, b: Int", "a + b >= 1000", "+"},
                new String[] {"a: Int, s: String", "String.length(s) <= a", "length"},
                new String[] {"from: Date, to: Date", "Date.daysBetween(from, to) >= 3", "from"},
                new String[] {"a: Decimal, b: Decimal", "Decimal.compare(a, b) <= 0", "p.a"})) {
            List<BorderAssessment> drawn = linesOf(compiled("""
                    data Pair = { %s }
                        invariant %s
                    """.formatted(related[0], related[1]), "p: Pair", List.of("Ok"), ""));
            assertTrue(drawn.stream().anyMatch(each -> each.axis().contains(related[2])),
                    related[1] + ": " + describe(drawn));
        }
    }

    private static String describe(List<BorderAssessment> lines) {
        return lines.stream().map(each -> each.axis() + " @ " + each.value()).toList().toString();
    }

    /**
     * An end of the type the relation comes out one way at only because the partner would pass
     * where the type stops is no class, for a product as for an order. A factor held to the least
     * {@code Int} and the one above it fails {@code a * b >= 1000} at the least whatever {@code b}
     * the run can multiply it by, and draws no line there, as a value held to the greatest
     * {@code Int} and the one below it fails {@code x < y} at the greatest and draws none.
     */
    @Test
    void anEndOfTheTypeIsNoClassOfAProductAsOfAnOrder() {
        Map<String, List<String>> product = classesOf(measured(compiled("""
                data Low = Int
                    invariant value <= -9223372036854775807
                """, "a: Low, b: Int", "a.value * b >= 1000")));
        assertTrue(!product.containsKey("a"), product.toString());

        Map<String, List<String>> order = classesOf(measured(compiled("""
                data High = Int
                    invariant value >= 9223372036854775806
                """, "x: High, y: Int", "x.value < y")));
        assertTrue(!order.containsKey("x"), order.toString());
    }

    /**
     * A row whose product passes where the type stops has no product, which is not the exact
     * arithmetic failing to hold one: the run stops there, and the row stands on neither side of a
     * line on the product. The least value times one and the greatest times one are products; the
     * least times minus one and the greatest times two are not.
     */
    @Test
    void aProductPastWhereTheTypeStopsIsNone() {
        NumericTerm x = new NumericTerm.ValueOf(TermPath.of("x"));
        NumericTerm y = new NumericTerm.ValueOf(TermPath.of("y"));
        long least = Long.MIN_VALUE;
        long greatest = Long.MAX_VALUE;
        assertEquals(Optional.empty(), productOf(x, y, least, -1));
        assertEquals(Optional.empty(), productOf(x, y, greatest, 2));
        assertEquals(Optional.of(ExactRatio.of(least)), productOf(x, y, least, 1));
        assertEquals(Optional.of(ExactRatio.of(greatest)), productOf(x, y, greatest, 1));
        assertEquals(Optional.of(ExactRatio.ZERO), productOf(x, y, least, 0));
    }

    private static Optional<ExactRatio> productOf(NumericTerm x, NumericTerm y, long one,
                                                  long other) {
        Map<NumericTerm, Place> values = new LinkedHashMap<>();
        values.put(x, Count.of(one));
        values.put(y, Count.of(other));
        return OrderedAffineBoundary.productAt(List.of(x, y), values)
                instanceof ExactAnswer.Held<Optional<ExactRatio>>(var product) ? product : null;
    }

    /** One row of a measurement: what each input was written as and what each point is for. */
    private record Row(List<String> inputs, List<String> labels) {}

    private static List<Row> certifiedRows(List<BorderAssessment> lines) {
        List<Row> rows = new ArrayList<>();
        for (BorderAssessment border : lines) {
            for (ItemAssessment item : border.items().values()) {
                if (!(item instanceof ItemAssessment.Owed owed)) {
                    continue;
                }
                for (ItemAssessment.Attempt attempt : owed.searches().each()) {
                    if (attempt instanceof ItemAssessment.Attempt.Certified certified) {
                        List<String> labels = new ArrayList<>();
                        certified.row().purposes().forEach(each -> labels.addAll(each.labels()));
                        rows.add(new Row(certified.row().inputs().stream()
                                .map(each -> each.text()).toList(), labels));
                    }
                }
            }
        }
        return rows;
    }

    private static List<BorderAssessment> linesOf(Compilation compilation) {
        Map<String, List<BorderAssessment>> read = Adequacy.readingsOf(compilation.db(), "demo");
        assertNotNull(read, "the model under test compiles");
        List<BorderAssessment> lines = read.get("f");
        assertNotNull(lines, "f was measured");
        return lines;
    }

    /** The values the lines of the product are drawn at, leaving out the lines on one factor. */
    private static List<String> bordersOf(List<BorderAssessment> lines) {
        return lines.stream().filter(each -> each.axis().contains(" * "))
                .map(BorderAssessment::value).toList();
    }

    private static PartitionEvidence measured(Compilation compilation) {
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, "the model under test compiles");
        PartitionEvidence evidence = coverage.get("f");
        assertNotNull(evidence, "f was measured");
        return evidence;
    }

    /** The classes of each axis, by the path of the position it divides. */
    private static Map<String, List<String>> classesOf(PartitionEvidence evidence) {
        Map<String, List<String>> out = new LinkedHashMap<>();
        evidence.axes().forEach(axis -> out.put(axis.path(), axis.classes()));
        return out;
    }

    private static List<UndividedPosition.Reason> reasonsOf(PartitionEvidence evidence) {
        return evidence.notRead().stream().map(PartitionEvidence.NotRead::reason).distinct()
                .toList();
    }

    private static Compilation compiled(String prelude, String parameters, String condition) {
        return compiled(prelude, parameters, List.of("guard " + condition + " else No", "Ok"), "");
    }

    /** {@code f} over {@code parameters}, its body the lines given, after the declarations
     *  {@code prelude} writes and with the examples after it. */
    private static Compilation compiled(String prelude, String parameters, List<String> body,
                                        String examples) {
        String model = """
                module demo

                data Ok
                data No

                %s

                behavior f : (%s) -> Ok | No
                let f (%s) = {
                    %s
                }
                %s
                """.formatted(prelude, parameters,
                parameters.replaceAll(":\\s*[A-Za-z<>]+", ""), String.join("\n    ", body),
                examples);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
