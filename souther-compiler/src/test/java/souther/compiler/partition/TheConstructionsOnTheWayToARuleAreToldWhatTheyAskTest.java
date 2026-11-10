package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.DocumentShape;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A construction a run works out on the way to a rule asks something of the run: the numbers it is
 * made of have to lie where the clauses of its type leave them, and a run that does not meet that
 * stops there. The rows the rule is read over are narrowed by the condition, and the report says
 * what it was, from the same condition, once for each construction as the model wrote it.
 *
 * <p>Where the declarations already hold the condition nothing is asked of a run, and nothing is
 * said.
 */
class TheConstructionsOnTheWayToARuleAreToldWhatTheyAskTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String HEAD = """
            module demo

            data Refund = Decimal
                invariant value >= 0.0m

            data Gross = Decimal
                invariant value >= 0.0m

            data Rate = Decimal
                invariant value >= 0.0m && value <= 1.0m

            data Out = { refund: Refund, fee: Refund, within: Bool }

            """;

    private static String plan(String parameters, String gross, String rate, String fee) {
        return HEAD + """
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
                """.formatted(parameters, gross, rate, gross, fee);
    }

    private static final String UNTYPED = plan("gross: Decimal, rate: Decimal, limit: Decimal",
            "gross", "rate", "Decimal.min(fee, gross)");

    /** What the report says each construction asks, as the document writes it. */
    private static List<JsonNode> asksOf(Compilation compilation) {
        JsonNode report = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        DocumentShape.assertShapedLikeTheSchema(report);
        List<JsonNode> out = new ArrayList<>();
        collect(report, out);
        return out;
    }

    private static void collect(JsonNode node, List<JsonNode> out) {
        if (node.isObject() && node.path("kind").asString().equals("rule_may_stop_a_run")
                && node.has("asks")) {
            node.get("asks").forEach(out::add);
        }
        node.forEach(child -> collect(child, out));
    }

    private static Compilation compiled(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertTrue(compilation.errors().isEmpty(), () -> "compiles: " + compilation.errors());
        return compilation;
    }

    private static String human(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).toString();
    }

    private static JsonNode is(String form, String is, String than) {
        return JSON.readTree("{\"form\":\"%s\",\"is\":\"%s\",\"than\":\"%s\"}"
                .formatted(form, is, than));
    }

    /**
     * The construction that stops a run for a negative rate where the gross is above nought: what
     * it asks is the product and the gross at nought or above, said of the construction written at
     * the line it is, in the document and in the words beside the rule.
     */
    @Test
    void aConstructionSaysWhatItAsksInTheDocumentAndInTheWordsBesideTheRule() {
        Compilation compilation = compiled(UNTYPED);
        List<JsonNode> asks = asksOf(compilation);
        assertEquals(1, asks.size(), asks.toString());
        assertEquals("Refund", asks.getFirst().path("construction").asString());
        JsonNode asked = asks.getFirst().path("asked");
        assertEquals(List.of(is("gross * rate", "at_least", "0"), is("gross", "at_least", "0")),
                List.copyOf(asked.path("allOf").values()));
        assertTrue(Pattern.compile("a run gets past Refund at [0-9]+:[0-9]+ only where"
                        + " gross \\* rate is at least 0 and gross is at least 0")
                .matcher(human(compilation)).find(), human(compilation));
    }

    /** A condition the declarations hold of every value says nothing: a gross at nought or above
     *  and a rate from nought to one leave the fee and the gross at nought or above. */
    @Test
    void whatTheDeclarationsHoldIsAskedOfNoRun() {
        Compilation compilation = compiled(plan("gross: Gross, rate: Rate, limit: Decimal",
                "gross.value", "rate.value", "Decimal.min(fee, gross.value)"));
        assertEquals(List.of(), asksOf(compilation));
        assertTrue(!human(compilation).contains("a run gets past"), human(compilation));
    }

    /** Of the two that the declarations do not hold, only that one is asked: the gross is held at
     *  nought or above, and the product is what is left. */
    @Test
    void ofTwoConditionsOnlyWhatTheDeclarationsDoNotHoldIsAsked() {
        Compilation compilation = compiled(plan("gross: Gross, rate: Decimal, limit: Decimal",
                "gross.value", "rate", "Decimal.min(fee, gross.value)"));
        List<JsonNode> asks = asksOf(compilation);
        assertEquals(1, asks.size(), asks.toString());
        assertEquals(is("gross * rate", "at_least", "0"), asks.getFirst().path("asked"));
    }

    /** The greater of two is at nought or above where either is, which is one condition of two
     *  alternatives and not two conditions. */
    @Test
    void theGreaterOfTwoAsksThatEitherIsAtNoughtOrAbove() {
        Compilation compilation = compiled("""
                module demo

                data Held = Decimal
                    invariant value >= 0.0m
                data Plan = { p: Held, within: Bool }

                behavior f : (x: Decimal, y: Decimal, c: Decimal) -> Plan
                    constructs Plan, Held
                let f (x, y, c) = Plan {
                    p = Held(Decimal.max(x, y)),
                    within = Decimal.compare(x, c) <= 0
                }
                """);
        List<JsonNode> asks = asksOf(compilation);
        assertEquals(1, asks.size(), asks.toString());
        assertEquals(List.of(is("x", "at_least", "0"), is("y", "at_least", "0")),
                List.copyOf(asks.getFirst().path("asked").path("oneOf").values()));
        assertTrue(human(compilation).contains("only where x is at least 0 or y is at least 0"),
                human(compilation));
    }

    /** Two constructions that ask the same are two places a run may stop, and are two. */
    @Test
    void twoConstructionsThatAskTheSameAreTwo() {
        Compilation compilation = compiled("""
                module demo

                data Held = Decimal
                    invariant value >= 0.0m
                data Plan = { p: Held, q: Held, within: Bool }

                behavior f : (x: Decimal, c: Decimal) -> Plan
                    constructs Plan, Held
                let f (x, c) = Plan {
                    p = Held(Decimal.min(x, 1.0m)),
                    q = Held(Decimal.min(x, 2.0m)),
                    within = Decimal.compare(x, c) <= 0
                }
                """);
        List<JsonNode> asks = asksOf(compilation);
        assertEquals(2, asks.size(), asks.toString());
        assertTrue(!asks.get(0).path("at").equals(asks.get(1).path("at")), asks.toString());
        assertEquals(asks.get(0).path("asked"), asks.get(1).path("asked"));
    }

    /**
     * A rule is told what the constructions ask of the places it reads and no others: a construction
     * over other places asks the same of the run and bears on nothing read here, and said under
     * every rule it would be said once for each rule.
     */
    @Test
    void aRuleIsToldOnlyWhatIsAskedOfThePlacesItReads() {
        Compilation compilation = compiled("""
                module demo

                data Held = Decimal
                    invariant value >= 0.0m
                data Plan = { p: Held, q: Held, wx: Bool, wy: Bool }

                behavior f : (x: Decimal, y: Decimal, c: Decimal) -> Plan
                    constructs Plan, Held
                let f (x, y, c) = Plan {
                    p = Held(Decimal.min(x, 1.0m)),
                    q = Held(Decimal.min(y, 1.0m)),
                    wx = Decimal.compare(x, c) <= 0,
                    wy = Decimal.compare(y, c) <= 0
                }
                """);
        JsonNode report = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        List<List<JsonNode>> perRule = new ArrayList<>();
        collectPerFinding(report, perRule);
        assertEquals(2, perRule.size(), perRule.toString());
        for (List<JsonNode> asks : perRule) {
            assertEquals(1, asks.size(), asks.toString());
        }
        assertTrue(!perRule.get(0).getFirst().path("at").equals(perRule.get(1).getFirst().path("at")),
                perRule.toString());
    }

    private static void collectPerFinding(JsonNode node, List<List<JsonNode>> out) {
        if (node.isObject() && node.path("kind").asString().equals("rule_may_stop_a_run")
                && node.has("asks")) {
            out.add(List.copyOf(node.get("asks").values()));
        }
        node.forEach(child -> collectPerFinding(child, out));
    }

    private static String madeOf(String number) {
        return """
                module demo

                data Held = Decimal
                    invariant value >= 0.0m
                data Plan = { p: Held, within: Bool }

                behavior f : (x: Decimal, y: Decimal, c: Decimal) -> Plan
                    constructs Plan, Held
                let f (x, y, c) = Plan {
                    p = Held(NUMBER),
                    within = Decimal.compare(x, c) <= 0
                }
                """.replace("NUMBER", number);
    }

    /**
     * A part of what is asked that is only a constant settles what it is a part of: the greater
     * of {@code -1} and a number is at nought or above where the number is, which is what is
     * asked and not nothing; the greater of {@code 1} and a number is at nought or above whatever
     * the number is, which is nothing asked; and the lesser of {@code 1} and a number is at nought
     * or above where the number is.
     */
    @Test
    void aConstantPartSettlesWhatItIsAPartOfAndIsNeverNothingAsked() {
        assertEquals(List.of(is("x", "at_least", "0")),
                asksOf(compiled(madeOf("Decimal.max(-1.0m, x)"))).stream()
                        .map(one -> one.path("asked")).toList());
        assertEquals(List.of(), asksOf(compiled(madeOf("Decimal.max(1.0m, x)"))));
        assertEquals(List.of(is("x", "at_least", "0")),
                asksOf(compiled(madeOf("Decimal.min(1.0m, x)"))).stream()
                        .map(one -> one.path("asked")).toList());
    }

    /**
     * What the way to the rule holds is not asked of a run that gets there: under a guard that
     * keeps the number at nought or above, the construction in the branch stops no run, and no
     * rule is said to be one a run may stop in for it. Where the guard holds only some of what is
     * asked, what is left is what is said.
     */
    @Test
    void whatTheGuardsOnTheWayHoldIsNotAskedOfARunThatGetsPast() {
        String under = """
                module demo

                data Held = Decimal
                    invariant value >= 0.0m
                data Plan = { p: Held, within: Bool }

                behavior f : (x: Decimal, y: Decimal, c: Decimal) -> Plan
                    constructs Plan, Held
                let f (x, y, c) =
                    if GUARD then Plan { p = Held(NUMBER), within = Decimal.compare(x, c) <= 0 }
                    else Plan { p = Held(0.0m), within = false }
                """;
        assertEquals(List.of(), asksOf(compiled(under.replace("GUARD", "x >= 0.0m")
                .replace("NUMBER", "x"))));
        assertEquals(List.of(is("x", "at_least", "0")), asksOf(compiled(
                under.replace("GUARD", "y >= 0.0m").replace("NUMBER", "x"))).stream()
                .map(one -> one.path("asked")).toList());
        assertEquals(List.of(is("y", "at_least", "0")), asksOf(compiled(
                under.replace("GUARD", "x >= 0.0m").replace("NUMBER", "Decimal.min(x, y)")))
                .stream().map(one -> one.path("asked")).toList());
    }

    /**
     * A number is written the one way a number is written wherever it is exact, and that is not
     * always a decimal written out: a number the type holds apart from nought by a thousand
     * places is a power of ten. What the schema says of it is what every exact number in the
     * document says, so a document of such a number is still one the schema accepts.
     */
    @Test
    void aNumberTooLongToWriteOutIsTheSchemasAsMuchAsAnyOther() {
        String wide = "1" + "0".repeat(1001) + ".0m";
        Compilation compilation = compiled("""
                module demo

                data Held = Decimal
                    invariant value >= WIDE
                data Plan = { p: Held, within: Bool }

                behavior f : (x: Decimal, c: Decimal) -> Plan
                    constructs Plan, Held
                let f (x, c) = Plan {
                    p = Held(Decimal.max(x, 0.0m)),
                    within = Decimal.compare(x, c) <= 0
                }
                """.replace("WIDE", wide));
        List<JsonNode> asks = asksOf(compilation);
        assertEquals(1, asks.size(), asks.toString());
        assertTrue(!asks.getFirst().path("asked").path("than").asString().matches(
                "^-?[0-9]+(\\.[0-9]+)?$"), asks.toString());
    }

    /** What an {@code Int} construction asks is asked as a decimal number too. */
    @Test
    void anIntConstructionAsksItToo() {
        Compilation compilation = compiled("""
                module demo

                data Count = Int
                    invariant value >= 0
                data Plan = { n: Count, within: Bool }

                behavior f : (x: Int, c: Int) -> Plan
                    constructs Plan, Count
                let f (x, c) = Plan { n = Count(x), within = x <= c }
                """);
        List<JsonNode> asks = asksOf(compilation);
        assertEquals(1, asks.size(), asks.toString());
        assertEquals("Count", asks.getFirst().path("construction").asString());
        assertEquals(is("x", "at_least", "0"), asks.getFirst().path("asked"));
    }
}
