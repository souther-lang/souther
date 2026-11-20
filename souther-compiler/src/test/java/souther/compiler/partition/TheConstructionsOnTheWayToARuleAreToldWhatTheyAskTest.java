package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.ACompiledModel;
import souther.compiler.DocumentShape;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A construction a run works out on the way to a rule asks something of the run: the numbers it is
 * made of have to lie where the clauses of its type leave them, and a run that does not meet that
 * stops there. The rows the rule is read over are narrowed by the condition, and the report says
 * what it was, from the same condition, once for each construction as the model wrote it: as a
 * stop shown where some admissible run on the way does not meet it, and as not resolved where
 * that is not shown.
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
        JsonNode report = document(compilation);
        DocumentShape.assertShapedLikeTheSchema(report);
        List<JsonNode> out = new ArrayList<>();
        collect(report, out);
        return out;
    }

    private static void collect(JsonNode node, List<JsonNode> out) {
        JsonNode said = toldOf(node);
        if (said != null) {
            said.forEach(out::add);
        }
        node.forEach(child -> collect(child, out));
    }

    /**
     * What a finding says the constructions on the way ask, whether a run is shown to stop at
     * them ({@code constructions} of {@code rule_may_stop_a_run}) or that is not resolved
     * ({@code asks} of {@code rule_stop_not_shown}); null where it says none.
     */
    private static JsonNode toldOf(JsonNode node) {
        if (!node.isObject()) {
            return null;
        }
        return switch (node.path("kind").asString()) {
            case "rule_stop_not_shown" -> node.get("asks");
            case "rule_may_stop_a_run" -> node.get("constructions");
            default -> null;
        };
    }

    /** The document the report writes of {@code compilation}, written once for every reading a
     *  test makes of it. */
    private static JsonNode document(Compilation compilation) {
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
    }

    /** What the findings of {@code kind} in {@code report} say the constructions on the way
     *  ask. */
    private static List<JsonNode> toldIn(JsonNode report, String kind) {
        List<JsonNode> out = new ArrayList<>();
        collectOfKind(report, kind, out);
        return out;
    }

    private static void collectOfKind(JsonNode node, String kind, List<JsonNode> out) {
        if (node.isObject() && node.path("kind").asString().equals(kind) && toldOf(node) != null) {
            toldOf(node).forEach(out::add);
        }
        node.forEach(child -> collectOfKind(child, kind, out));
    }

    private static Compilation compiled(String model) {
        return ACompiledModel.measured(model, new Adequacy.Asked(Adequacy.Level.OFF, false));
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
                .matcher(human(compilation)).find(), () -> human(compilation));
    }

    /** A condition the declarations hold of every value says nothing: a gross at nought or above
     *  and a rate from nought to one leave the fee and the gross at nought or above. */
    @Test
    void whatTheDeclarationsHoldIsAskedOfNoRun() {
        Compilation compilation = compiled(plan("gross: Gross, rate: Rate, limit: Decimal",
                "gross.value", "rate.value", "Decimal.min(fee, gross.value)"));
        assertEquals(List.of(), asksOf(compilation));
        assertTrue(!human(compilation).contains("a run gets past"), () -> human(compilation));
        assertEveryOneSafe(compilation, "plan", 2);
    }

    /** That {@code behavior} has {@code howMany} constructions on the way to its rules and every
     *  one of them is judged to stop no run: asked about, and not left out. */
    private static void assertEveryOneSafe(Compilation compilation, String behavior,
                                           int howMany) {
        Map<Integer, Set<String>> judged = ConstructionsJudged.of(compilation, behavior);
        assertEquals(howMany, judged.size(), judged::toString);
        assertEquals(Set.of(Set.of("Safe")), Set.copyOf(judged.values()), judged::toString);
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
                () -> human(compilation));
    }

    /**
     * Of two constructions that ask the same, a run stops at the first, and the second asks
     * nothing of a run that gets to it, which got past the first: the first is said, and the
     * second is not.
     */
    @Test
    void ofTwoConstructionsThatAskTheSameOnlyTheFirstStopsARun() {
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
        JsonNode report = document(compilation);
        List<JsonNode> asks = toldIn(report, "rule_may_stop_a_run");
        assertEquals(1, asks.size(), asks.toString());
        assertEquals(10, asks.getFirst().path("at").path("line").asInt(), asks.toString());
        assertEquals(List.of(), toldIn(report, "rule_stop_not_shown"));
        assertEquals(Set.of("Safe"), ConstructionsJudged.of(compilation, "f").get(11));
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
        JsonNode said = toldOf(node);
        if (said != null) {
            out.add(List.copyOf(said.values()));
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
        Compilation settled = compiled(madeOf("Decimal.max(1.0m, x)"));
        assertEquals(List.of(), asksOf(settled));
        assertEveryOneSafe(settled, "f", 1);
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
        Compilation held = compiled(under.replace("GUARD", "x >= 0.0m").replace("NUMBER", "x"));
        assertEquals(List.of(), asksOf(held));
        assertEquals(Set.of("Safe"), ConstructionsJudged.of(held, "f").get(10));
        assertEquals(List.of(is("x", "at_least", "0")), asksOf(compiled(
                under.replace("GUARD", "y >= 0.0m").replace("NUMBER", "x"))).stream()
                .map(one -> one.path("asked")).toList());
        assertEquals(List.of(is("y", "at_least", "0")), asksOf(compiled(
                under.replace("GUARD", "x >= 0.0m").replace("NUMBER", "Decimal.min(x, y)")))
                .stream().map(one -> one.path("asked")).toList());
    }

    /** A bound a {@code Decimal} can pass is asked of it, though both ends of an {@code Int}
     *  meet it. */
    @Test
    void aDecimalBoundBeyondTheEndsOfAnIntIsAsked() {
        Compilation compilation = compiled("""
                module demo

                data Wide = Decimal
                    invariant value >= -100000000000000000000.0m
                data Out = { v: Wide, within: Bool }

                behavior f : (x: Decimal, c: Decimal) -> Out
                    constructs Out, Wide
                let f (x, c) = Out { v = Wide(x), within = Decimal.compare(x, c) <= 0 }
                """);
        assertEquals(List.of(is("x", "at_least", "-100000000000000000000")),
                asksOf(compilation).stream().map(one -> one.path("asked")).toList());
    }

    /** A guard met only after the construction does not leave anything out of what it asks. */
    @Test
    void aGuardAfterTheConstructionLeavesNothingOutOfWhatItAsks() {
        Compilation compilation = compiled("""
                module demo

                data Held = Decimal
                    invariant value >= 0.0m
                data Plan = { p: Held, within: Bool }

                behavior f : (x: Decimal, c: Decimal) -> Plan
                    constructs Plan, Held
                let f (x, c) = {
                    let made = Held(x)
                    if x >= 0.0m then Plan { p = made, within = Decimal.compare(x, c) <= 0 }
                    else Plan { p = Held(0.0m), within = false }
                }
                """);
        assertEquals(List.of(is("x", "at_least", "0")),
                asksOf(compilation).stream().map(one -> one.path("asked")).toList());
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

    /**
     * A construction some admissible run on the way does not meet is a stop shown: said of the
     * rule as one a run may stop on the way to, with what it asks, and not as one whose stop is
     * not resolved.
     */
    @Test
    void aConstructionSomeAdmissibleRunDoesNotMeetIsAStopShown() {
        Compilation compilation = compiled(madeOf("x"));
        JsonNode report = document(compilation);
        assertEquals(List.of(is("x", "at_least", "0")),
                toldIn(report, "rule_may_stop_a_run").stream()
                        .map(one -> one.path("asked")).toList());
        assertEquals(List.of(), toldIn(report, "rule_stop_not_shown"));
        assertTrue(Pattern.compile("may stop a run: [^\\n]* some admissible run stops at a "
                        + "construction on the way to this rule[^\\n]*; a run gets past Held at "
                        + "[0-9]+:[0-9]+ only where x is at least 0")
                .matcher(human(compilation)).find(), () -> human(compilation));
    }

    /**
     * A rule in the body of a helper read at each call of it, as one walking a list by its head
     * is, has what a run works out before it unread: a construction written before it in that
     * body is said as one no run is shown to get to, and never left out.
     */
    @Test
    void aConstructionBeforeARuleInAHelperReadAtItsCallIsNotLeftOut() {
        Compilation compilation = compiled("""
                module demo

                data Held = Decimal
                    invariant value >= 0.0m
                data Plan = { within: Bool }

                behavior f : (xs: List<Decimal>, c: Decimal) -> Plan
                    constructs Plan, Held
                let f (xs, c) = Plan { within = every(xs, c) }

                partial let every (xs: List<Decimal>, c: Decimal): Bool = match List.get(0, xs) with
                    | None -> true
                    | Some x -> {
                        let h = Held(x)
                        Decimal.compare(h.value, c) <= 0 && every(List.drop(1, xs), c)
                    }
                """);
        assertEquals(List.of("Held: reach_not_shown"), asksOf(compilation).stream()
                .map(one -> one.path("construction").asString() + ": "
                        + one.path("reason").asString())
                .distinct().toList());
    }

    /**
     * A construction on an arm whose condition holds what it asks stops no run that takes the arm:
     * it is among the constructions on the way to the rule after it, and judged to stop none.
     */
    @Test
    void aConstructionOnAnArmThatHoldsWhatItAsksIsJudgedSafe() {
        Compilation compilation = compiled("""
                module demo

                data Refund = Decimal
                    invariant value >= 0.0m
                data Out = { refund: Refund, within: Bool }

                behavior plan : (gross: Decimal, rate: Decimal, limit: Decimal) -> Out
                    constructs Out, Refund
                let plan (gross, rate, limit) = {
                    let net = if Decimal.compare(gross, rate) <= 0 then Refund(0.0m)
                        else Refund(Decimal.subtract(gross, rate))
                    Out { refund = net, within = Decimal.compare(gross, limit) <= 0 }
                }
                """);
        assertEveryOneSafe(compilation, "plan", 2);
    }

    /**
     * A construction after one whose condition is not read is not shown to stop a run, since the
     * one before may end it first, and is said as not resolved for that reason; the one before is
     * said for its own, and not left out.
     */
    @Test
    void aConstructionAfterOneNotReadIsNotResolved() {
        Compilation compilation = compiled(HEAD + """
                data Span = { lo: Decimal, hi: Decimal }
                    invariant lo <= hi

                behavior plan : (gross: Decimal, limit: Decimal) -> Out
                    constructs Out, Refund, Span

                let plan (gross, limit) = {
                    let span = Span { lo = gross, hi = limit }
                    Out {
                        refund = Refund(gross),
                        fee = Refund(0.0m),
                        within = Decimal.compare(span.lo, span.hi) <= 0
                    }
                }
                """);
        assertEquals(List.of("Span: asks_not_read", "Refund: something_before_it_may_stop"),
                asksOf(compilation).stream()
                        .map(one -> one.path("construction").asString() + ": "
                                + one.path("reason").asString())
                        .toList());
        assertTrue(Pattern.compile("stop not resolved: [^\\n]*; whether a run stops at Span at "
                        + "[0-9]+:[0-9]+ is not determined: what its type requires of the values "
                        + "it is made of is not read")
                .matcher(human(compilation)).find(), () -> human(compilation));
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
