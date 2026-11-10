package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.report.AdequacyReport;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A construction of a number stops a run at the numbers outside the run its type's clauses leave.
 * Where every number the places it reads can hold is inside that run, it stops none; where the
 * region of the search can carry what it asks, the run is narrowed by it and the rows the compiler
 * certifies keep to it; and where it can do neither, the places are not shown reached at every
 * value.
 */
class AConstructionTheReadRegionSatisfiesDoesNotEndTheRunTest {

    private static final String READ = "rule_relating_two_values";

    private static final String NOT_SHOWN = "relation_not_shown_reached_at_every_value";

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final Pattern A_NUMBER = Pattern.compile("-?[0-9]+(\\.[0-9]+)?");

    private static final String TYPES = """
            module demo

            data Refund = Decimal
                invariant value >= 0.0m

            data Gross = Decimal
                invariant value >= 0.0m

            data Rate = Decimal
                invariant value >= 0.0m && value <= 1.0m

            data Out = { refund: Refund, fee: Refund, within: Bool }

            """;

    private static final String UNTYPED = "gross: Decimal, rate: Decimal, limit: Decimal";

    private static final String TYPED = "gross: Gross, rate: Rate, limit: Decimal";

    private static final String GROSS_ONLY = "gross: Gross, rate: Decimal, limit: Decimal";

    private static final String RATE_ONLY = "gross: Decimal, rate: Rate, limit: Decimal";

    /** {@code plan} over {@code parameters}, whose fee is the construction {@code feeSource}. */
    private static String plan(String parameters, String gross, String rate, String feeSource) {
        return TYPES + """
                behavior plan : (%s) -> Out
                    constructs Out, Refund

                let plan (gross, rate, limit) = {
                    let fee = Decimal.multiply(%s, %s)
                    let net = Decimal.max(0.0m, Decimal.subtract(%s, fee))
                    Out {
                        refund = Refund(net),
                        fee = Refund(%s),
                        within = Decimal.compare(net, limit) <= 0
                    }
                }
                """.formatted(parameters, gross, rate, gross, feeSource);
    }

    private static Compilation compiled(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertTrue(compilation.errors().isEmpty(), () -> "compiles: " + compilation.errors());
        return compilation;
    }

    /** The places read by a rule, and the reasons a rule is not read at each of them. */
    private static Map<String, Set<String>> readingsOf(String model) {
        return readingsOf(compiled(model));
    }

    private static Map<String, Set<String>> readingsOf(Compilation compilation) {
        JsonNode report = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        Map<String, Set<String>> found = new LinkedHashMap<>();
        collect(report, found);
        found.values().forEach(each -> each.remove("rule_never_turns_on_this_line"));
        found.values().removeIf(Set::isEmpty);
        return found;
    }

    /** What is said of the named places only. */
    private static Map<String, Set<String>> at(Map<String, Set<String>> readings,
                                               String... places) {
        Map<String, Set<String>> out = new LinkedHashMap<>(readings);
        out.keySet().retainAll(Set.of(places));
        return out;
    }

    private static Map<String, Set<String>> bothPlaces(String reason) {
        return Map.of("gross", Set.of(reason), "rate", Set.of(reason));
    }

    /** The numbers of every row the compiler certifies for {@code f}, in the order of its
     *  parameters. */
    private static List<List<BigDecimal>> certifiedRowsOf(Compilation compilation,
                                                          String behavior) {
        List<List<BigDecimal>> out = new ArrayList<>();
        for (BorderAssessment border
                : Adequacy.readingsOf(compilation.db(), "demo").get(behavior)) {
            for (ItemAssessment item : border.items().values()) {
                if (!(item instanceof ItemAssessment.Owed owed)) {
                    continue;
                }
                for (ItemAssessment.Attempt attempt : owed.searches().each()) {
                    if (attempt instanceof ItemAssessment.Attempt.Certified certified) {
                        List<BigDecimal> row = new ArrayList<>();
                        certified.row().inputs().forEach(each -> {
                            Matcher found = A_NUMBER.matcher(each.text());
                            assertTrue(found.find(), each.text());
                            row.add(new BigDecimal(found.group()));
                        });
                        out.add(row);
                    }
                }
            }
        }
        assertTrue(!out.isEmpty(), "some row is certified");
        return out;
    }

    /**
     * What stops the run is the product of the two being at nought or above, and nothing holds it
     * beforehand: a negative rate is refused where the gross is above nought. The region carries
     * the product, so the run is narrowed by it, the places are read, and no row the compiler
     * certifies is one the construction refuses.
     */
    @Test
    void aStopTheRegionCarriesNarrowsTheRunAndTheRowsKeepToIt() {
        Compilation compilation = compiled(plan(UNTYPED, "gross", "rate",
                "Decimal.min(fee, gross)"));
        assertEquals(bothPlaces(READ), at(readingsOf(compilation), "gross", "rate"));
        for (List<BigDecimal> row : certifiedRowsOf(compilation, "plan")) {
            BigDecimal gross = row.get(0);
            assertTrue(gross.signum() >= 0 && gross.multiply(row.get(1)).signum() >= 0,
                    "a row " + row + " is refused by Refund");
        }
    }

    /** Both ends of what the lesser of two is held to stand of each: a gross at nought or above
     *  and a rate between nought and one leave both the fee and the gross at nought or above. */
    @Test
    void theLesserOfTwoNumbersTheDeclarationsHoldToTheTypeStopsNoRun() {
        for (String feeSource : List.of("Decimal.min(fee, gross.value)", "fee", "gross.value",
                "Decimal.max(fee, gross.value)")) {
            assertEquals(bothPlaces(READ),
                    at(readingsOf(plan(TYPED, "gross.value", "rate.value", feeSource)),
                            "gross", "rate"), feeSource);
        }
    }

    /**
     * What one of the two is is not enough where the other one may be outside the run: the lesser
     * needs both. A gross at nought or above leaves the lesser of the fee and the gross at nought
     * or above where the fee is, and a rate that may be negative stops it, so the rows keep to a
     * product at nought or above.
     */
    @Test
    void theLesserNeedsBothToStand() {
        Compilation compilation = compiled(plan(GROSS_ONLY, "gross.value", "rate",
                "Decimal.min(fee, gross.value)"));
        assertEquals(bothPlaces(READ), at(readingsOf(compilation), "gross", "rate"));
        for (List<BigDecimal> row : certifiedRowsOf(compilation, "plan")) {
            assertTrue(row.get(0).multiply(row.get(1)).signum() >= 0,
                    "a row " + row + " is refused by Refund");
        }
    }

    /**
     * A rate between nought and one leaves the product at nought or above wherever the gross is,
     * so what is left to stop the run is a gross at nought or above, which the run narrows by.
     */
    @Test
    void whereTheDeclarationsHoldOneConjunctTheOtherIsWhatIsLeftOfTheStop() {
        Compilation compilation = compiled(plan(RATE_ONLY, "gross", "rate.value",
                "Decimal.min(fee, gross)"));
        assertEquals(bothPlaces(READ), at(readingsOf(compilation), "gross", "rate"));
        for (List<BigDecimal> row : certifiedRowsOf(compilation, "plan")) {
            assertTrue(row.get(0).signum() >= 0, "a row " + row + " is refused by Refund");
        }
    }

    /** A run with a hole in it is no run: {@code value /= 50.0m} is outside a run of two ends. */
    @Test
    void aRuleWithAHoleInItIsNotReadAsTheRunBetweenItsEnds() {
        String model = """
                module demo

                data Held = Decimal
                    invariant value >= 0.0m && value /= 50.0m
                data Plan = { p: Held, within: Bool }

                behavior f : (x: Decimal, c: Decimal) -> Plan
                    constructs Plan, Held
                let f (x, c) = {
                    let y = Decimal.max(0.0m, x)
                    Plan { p = Held(y), within = Decimal.compare(y, c) <= 0 }
                }
                """;
        assertEquals(Map.of("x", Set.of(NOT_SHOWN)), readingsOf(model));
    }

    /**
     * The statements of the way hold what the declarations do not: under a guard that keeps the
     * gross and the rate at nought or above, the construction in the branch asks nothing the way
     * does not hold, and under one that keeps only the gross it still asks a product at nought or
     * above, which the run is narrowed by.
     */
    @Test
    void aGuardOnTheWayHoldsWhatTheConstructionAsksOrLeavesItToTheRun() {
        Compilation both = compiled(guarded("gross >= 0.0m && rate >= 0.0m"));
        assertEquals(bothPlaces(READ), at(readingsOf(both), "gross", "rate"));
        Compilation onlyTheGross = compiled(guarded("gross >= 0.0m"));
        assertEquals(bothPlaces(READ), at(readingsOf(onlyTheGross), "gross", "rate"));
        for (List<BigDecimal> row : certifiedRowsOf(onlyTheGross, "plan")) {
            BigDecimal gross = row.get(0);
            BigDecimal rate = row.get(1);
            // The branch the guard keeps the row out of builds no construction that asks it.
            assertTrue(gross.signum() < 0 || gross.multiply(rate).signum() >= 0
                    || rate.signum() >= 0, "a row " + row + " is refused by Refund");
        }
    }

    /**
     * A total of numbers is a number of the run, and what the elements are held to bounds it: the
     * total of numbers at nought or above is at nought or above, and one construction of a fee from
     * it is held to the type or narrows the run, whichever the rate may be.
     */
    @Test
    void aTotalOfNumbersIsAskedAsOneNumberOfTheRun() {
        for (String element : List.of("Int", "Qty")) {
            for (String rate : List.of("Decimal", "NonNeg")) {
                assertEquals(Set.of("rate"), readsOf(totalOver(element, rate)), element + rate);
            }
        }
    }

    /**
     * The product of two numbers above nought is above nought, and one of two numbers at nought or
     * above is only at nought or above. Where the end is not reached the construction of a number
     * above nought is held to the type, and where it is the run is narrowed by it.
     */
    @Test
    void aProductIsAboveNoughtOnlyWhereBothFactorsAre() {
        for (List<String> factors : List.of(List.of("Open", "Open"), List.of("Open", "Closed"),
                List.of("Closed", "Closed"))) {
            assertEquals(Map.of("a", Set.of(READ), "b", Set.of(READ)),
                    at(readingsOf(strictProduct(factors.get(0), factors.get(1))), "a", "b"),
                    factors.toString());
        }
    }

    /**
     * One condition of a construction can follow from another and still stop the run: the lesser
     * of a number and one more than it is at nought or above where the number is, so what is left
     * of the stop is that number at nought or above, which the run narrows by and the rows keep to.
     */
    @Test
    void aConditionThatFollowsFromAnotherLeavesTheOtherAsTheStop() {
        Compilation compilation = compiled("""
                module demo

                data Held = Decimal
                    invariant value >= 0.0m
                data Plan = { p: Held, within: Bool }

                behavior f : (x: Decimal, c: Decimal) -> Plan
                    constructs Plan, Held
                let f (x, c) = Plan {
                    p = Held(Decimal.min(x, Decimal.add(x, 1.0m))),
                    within = Decimal.compare(x, c) <= 0
                }
                """);
        for (List<BigDecimal> row : certifiedRowsOf(compilation, "f")) {
            assertTrue(row.get(0).signum() >= 0, "a row " + row + " is refused by Held");
        }
    }

    private static String strictProduct(String a, String b) {
        return """
                module demo

                data Positive = Decimal
                    invariant value > 0.0m
                data Open = Decimal
                    invariant value > 0.0m
                data Closed = Decimal
                    invariant value >= 0.0m
                data Plan = { p: Positive, within: Bool }

                behavior f : (a: AT, b: BT, limit: Decimal) -> Plan
                    constructs Plan, Positive
                let f (a, b, limit) = {
                    let p = Decimal.multiply(a.value, b.value)
                    Plan { p = Positive(p), within = Decimal.compare(p, limit) <= 0 }
                }
                """.replace("AT", a).replace("BT", b);
    }

    private static Set<String> readsOf(String model) {
        Set<String> read = new TreeSet<>();
        readingsOf(model).forEach((position, reasons) -> {
            if (reasons.contains(READ) && position.equals("rate")) {
                read.add(position);
            }
        });
        return read;
    }

    private static String totalOver(String element, String rate) {
        String taken = element.equals("Int") ? "q" : "q.value";
        String rateValue = rate.equals("Decimal") ? "rate" : "rate.value";
        return """
                module demo

                data Refund = Decimal
                    invariant value >= 0.0m
                data Qty = Int
                    invariant value >= 0
                data NonNeg = Decimal
                    invariant value >= 0.0m
                data Out = { fee: Refund, within: Bool }

                behavior f : (m: Map<String, ELEMENT>, rate: RATETYPE, limit: Decimal) -> Out
                    constructs Out, Refund
                let f (m, rate, limit) = {
                    let gross = Decimal.fromInt(Map.fold((acc, k, q) -> acc + TAKEN, 0, m))
                    let fee = Decimal.multiply(gross, RATEVALUE)
                    Out {
                        fee = Refund(Decimal.min(fee, gross)),
                        within = Decimal.compare(fee, limit) <= 0
                    }
                }
                """.replace("ELEMENT", element).replace("RATETYPE", rate).replace("TAKEN", taken)
                .replace("RATEVALUE", rateValue);
    }

    private static String guarded(String guard) {
        return TYPES + """
                behavior plan : (gross: Decimal, rate: Decimal, limit: Decimal) -> Out
                    constructs Out, Refund

                let plan (gross, rate, limit) = {
                    if %s then {
                        let fee = Decimal.multiply(gross, rate)
                        let net = Decimal.max(0.0m, Decimal.subtract(gross, fee))
                        Out {
                            refund = Refund(net),
                            fee = Refund(Decimal.min(fee, gross)),
                            within = Decimal.compare(net, limit) <= 0
                        }
                    } else Out { refund = Refund(0.0m), fee = Refund(0.0m), within = false }
                }
                """.formatted(guard);
    }

    private static void collect(JsonNode node, Map<String, Set<String>> out) {
        if (node.isObject() && node.has("ruleId") && node.has("reason") && node.has("position")) {
            out.computeIfAbsent(node.path("position").asString(), _ -> new TreeSet<>())
                    .add(node.path("reason").asString());
        }
        node.forEach(child -> collect(child, out));
    }
}
