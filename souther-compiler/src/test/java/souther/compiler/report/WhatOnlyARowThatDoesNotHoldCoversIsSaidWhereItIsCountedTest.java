package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.DocumentShape;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row that does not hold is counted for what it reached, and a report says what only such rows
 * cover.
 *
 * <p>The count is not what changes. Whatever a row reached before it stopped, it reached, so an arm,
 * a class, a point, a rule or a combination it got to is met. What a reader is owed beside that
 * number is which of those the count has only through such rows — where nothing else covers them,
 * which is a different set from where the rows went.
 *
 * <p>Every page this class reads is also held to its own closing line: the number it says it marked
 * is the number of lines it marked.
 */
class WhatOnlyARowThatDoesNotHoldCoversIsSaidWhereItIsCountedTest {

    /** Four rows, one of which states the wrong answer. */
    private static final String FAILING = """
            data Celsius = Int

            behavior label : (t: Celsius) -> Cold | Warm

            let label (t) = if t.value < 24 then Cold else Warm

            example label
                | "23 is cold" : (Celsius(23)) -> Cold
                | "24 is warm" : (Celsius(24)) -> Cold
                | "10 is cold" : (Celsius(10)) -> Cold
                | "30 is warm" : (Celsius(30)) -> Warm
            """;

    /** The same without the one row that held at `Warm`, so the row that does not hold is all that
     *  reaches it. */
    private static final String ONLY = FAILING.replace(
            "    | \"30 is warm\" : (Celsius(30)) -> Warm\n", "");

    /** The same with the wrong answer put right. */
    private static final String HOLDING = FAILING.replace(
            "(Celsius(24)) -> Cold", "(Celsius(24)) -> Warm");

    /**
     * Where the row that does not hold is the only row through something, that something is named
     * beside the count — and only there.
     *
     * <p>The row at 24 goes through `else`, sits in the class above the line and takes the rule
     * that answers `Warm`, and the row at 30 does all three as well; the point at 24 nothing else
     * stands at. So one line is marked and three are not, which is the difference between where a
     * row went and what rests on it.
     */
    @Test
    void whatAnotherRowAlsoCoversIsNotMarked() {
        String human = human(FAILING);
        assertEquals(List.of("      ~ only a row that does not hold is at the OFF point"
                        + " (comparison@5:28): label 24 is warm (9:7)"),
                marked(human), human);
        assertTrue(human.contains("    border      borders 1   obligations 4/4\n"),
                () -> "and the point is still counted as met: " + human);
        assertTrue(human.contains("    branch      2/2\n"), human);
    }

    /**
     * Take the row that held at `Warm` away and everything it shared with the row at 24 rests on
     * the row at 24 alone.
     */
    @Test
    void whatOnlyTheRowThatDoesNotHoldReachesIsMarkedInEveryMeasure() {
        String human = human(ONLY);
        assertEquals(List.of(
                        "      ~ only a row that does not hold is in `t/24 <= x` at t:"
                                + " label 24 is warm (9:7)",
                        "      ~ only a row that does not hold is at the OFF point"
                                + " (comparison@5:28): label 24 is warm (9:7)",
                        "      ~ only a row that does not hold goes through `else` (5:17):"
                                + " label 24 is warm (9:7)",
                        "      ~ only a row that does not hold takes a decision rule:"
                                + " label 24 is warm (9:7)"),
                marked(human), human);
    }

    /**
     * The report ends on the rows that do not hold, each with where it stopped, whatever the verdict
     * above them says.
     *
     * <p>The verdict is unchanged: it answers whether the rows cover what the model owes, and a
     * row that does not hold covers what it reached. Said after it, because the last lines are what
     * a terminal or a build log leaves in front of a reader.
     */
    @Test
    void theReportEndsOnTheRowsThatDoNotHold() {
        String human = human(FAILING);
        assertTrue(human.endsWith("""
                adequacy: satisfied
                1 row does not hold:
                  label 24 is warm (0:9:7): the behavior answered otherwise
                1 obligation counted as met is covered only by rows that do not hold, marked `~`.
                """), human);
    }

    /**
     * A row that never applied the behavior is not said to have answered otherwise.
     *
     * <p>A row whose expectation could not be built stopped before the behavior was applied, and
     * what it covers is what its input reached. Named as a wrong answer, it would send an author to
     * the body for a mistake in the row.
     */
    @Test
    void whereARowStoppedIsSaidWithIt() {
        String model = HOLDING.replace("(Celsius(24)) -> Warm", "(Celsius(24)) -> Hot")
                .replace("data Celsius = Int\n", "data Celsius = Int\ndata Hot\n");
        String human = human(model);
        assertTrue(human.contains("label 24 is warm (0:10:7): what it expects could not be built\n"),
                human);
        JsonNode label = behavior(json(model), "label");
        assertEquals("expected_fixture",
                label.get("rowsThatDoNotHold").get(0).get("failedAt").asString(), label::toString);
    }

    /** And a report whose rows all hold says nothing of the kind. */
    @Test
    void rowsThatAllHoldAddNothing() {
        String human = human(HOLDING);
        assertEquals(List.of(), marked(human), human);
        assertFalse(human.contains("does not hold"), human);
        assertTrue(human.endsWith("adequacy: satisfied\n"), human);

        JsonNode root = json(HOLDING);
        assertEquals(0, behavior(root, "label").get("rowsThatDoNotHold").size(), root::toString);
        assertEquals(List.of(), onlyWitnessedBy(root));
    }

    /** Two rows that do not hold through one arm are both named, in the order they were read. */
    @Test
    void everyRowThatDoesNotHoldIsNamed() {
        String human = human(ONLY.replace("    | \"10 is cold\" : (Celsius(10)) -> Cold\n",
                "    | \"25 is warm\" : (Celsius(25)) -> Cold\n"));
        assertTrue(human.contains("      ~ only rows that do not hold go through `else` (5:17):"
                        + " label 24 is warm (9:7), label 25 is warm (10:7)\n"),
                human);
    }

    /**
     * A row waiting for its answer is another row, and the point it stands at rests on more than
     * the row that does not hold.
     *
     * <p>What the mark says is that the count has the point only through rows that do not hold. A
     * row whose answer is owed keeps it there, whatever it will be found to answer.
     */
    @Test
    void aRowWaitingForItsAnswerIsAnotherRow() {
        String human = human(FAILING.replace("    | \"10 is cold\" : (Celsius(10)) -> Cold\n",
                "    | \"24 again\" : (Celsius(24)) -> <?>\n"));
        assertFalse(human.contains("OFF point (comparison@5:28): label"), human);
    }

    /**
     * The document says the same thing as the page, in the shape the schema gives it.
     *
     * <p>The row is named by the key its behavior's `rowObligations` entry is under, so a consumer
     * joins the two without reading a name out of prose.
     */
    @Test
    void theDocumentNamesTheSameRowsAtTheSameObligations() {
        JsonNode root = json(ONLY);
        DocumentShape.assertShapedLikeTheSchema(root);
        JsonNode label = behavior(root, "label");
        JsonNode failing = label.get("rowsThatDoNotHold");
        assertEquals(1, failing.size(), failing::toString);
        assertEquals("24 is warm", failing.get(0).get("row").get("name").asString());
        assertEquals("label", failing.get(0).get("row").get("behavior").asString());
        assertEquals("comparison", failing.get(0).get("failedAt").asString());
        // One per measure the page marks, and every one of them the same row.
        List<JsonNode> named = onlyWitnessedBy(root);
        assertEquals(4, named.size(), named::toString);
        for (JsonNode rows : named) {
            assertEquals(1, rows.size(), rows::toString);
            assertEquals(failing.get(0), rows.get(0), rows::toString);
        }
    }

    /** Two positions held to their pairs, one row of which states the wrong answer. */
    private static final String PAIRS = """
            module probe.charge

            data Flat
            data Metered
            data Plan = Flat | Metered
            data Usage = Int
                invariant value >= 0
            data Fee = Int

            behavior charge : (plan: Plan, usage: Usage) -> Fee
                constructs Fee

            let charge (plan, usage) =
                match plan with
                    | Flat -> Fee(1000)
                    | Metered -> if usage.value <= 100 then Fee(300) else Fee(800)

            example charge
                | "flat"              : (Flat, Usage(0))      -> Fee(1000)
                | "metered, at 100"   : (Metered, Usage(100)) -> Fee(300)
                | "metered, past 100" : (Metered, Usage(101)) -> Fee(300)
            """;

    /**
     * A combination of two classes only a row that does not hold is in is marked, and a row that
     * holds in the same combination takes the mark away.
     */
    @Test
    void aCombinationOfClassesOnlyARowThatDoesNotHoldIsInIsMarked() {
        String human = human(PAIRS);
        assertTrue(human.contains("      ~ only a row that does not hold is in `Metered` at"
                + " charge/plan with `usage/100 < x` at charge/usage: charge metered, past 100"
                + " (21:7)\n"), human);
        JsonNode between = behavior(json(PAIRS), "charge").get("partition").get("pairs")
                .get("between").get(0);
        assertEquals("usage/100 < x", between.get("coveredOnlyBy").get(0).get("other").asString(),
                between::toString);

        String withAnother = PAIRS + "    | \"metered, at 200\" : (Metered, Usage(200))"
                + " -> Fee(800)\n";
        assertFalse(human(withAnother).contains("~ only a row that does not hold is in `Metered`"),
                withAnother);
        assertFalse(behavior(json(withAnother), "charge").get("partition").get("pairs")
                .get("between").get(0).has("coveredOnlyBy"));
    }

    /** A body whose decisions meet, one row of which states the wrong answer. */
    private static final String MEETINGS = """
            module example.shipping

            data Total = Int
            data Premium
            data Standard
            data Membership = Premium | Standard
            data Express
            data Regular
            data Delivery = Express | Regular
            data Fee = Int

            behavior shippingFee : (total: Total, member: Membership, delivery: Delivery) -> Fee
                constructs Fee

            let shippingFee (total, member, delivery) =
                Fee(baseFee(total, member) + expressFee(delivery))

            let baseFee (total: Total, member: Membership): Int =
                match member with
                    | Premium -> 0
                    | Standard -> if total.value >= 5000 then 0 else 500

            let expressFee (delivery: Delivery): Int =
                match delivery with
                    | Express -> 500
                    | Regular -> 0

            example shippingFee
                | (Total(0), Premium, Express)     -> Fee(500)
                | (Total(0), Standard, Regular)    -> Fee(500)
                | (Total(5000), Premium, Regular)  -> Fee(0)
                | (Total(5000), Standard, Express) -> Fee(9)
            """;

    /**
     * A combination of the decisions only a row that does not hold makes is marked, and a row that
     * holds making the same one takes the mark away.
     */
    @Test
    void aCombinationOfTheDecisionsOnlyARowThatDoesNotHoldMakesIsMarked() {
        String human = human(MEETINGS);
        assertTrue(human.contains("      ~ only a row that does not hold makes this combination of"
                + " the decisions: shippingFee #4 in 0 (32:7)\n"), human);
        assertEquals(1, onlyWitnessedByIn(behavior(json(MEETINGS), "shippingFee")
                .get("interaction")), MEETINGS);

        String withAnother = MEETINGS + "    | (Total(6000), Standard, Express) -> Fee(500)\n";
        assertFalse(human(withAnother).contains("makes this combination of the decisions:"),
                withAnother);
        assertEquals(0, onlyWitnessedByIn(behavior(json(withAnother), "shippingFee")
                .get("interaction")), withAnother);
    }

    /** A behavior whose body is another's, each with a row, and the row through the other's arm
     *  states the wrong answer. */
    private static final String THROUGH = """
            module example.trip

            data Amount = Int
                invariant value >= 0

            data Draft = { cost: Amount }
            data Submitted = { cost: Amount }
            data Waiting = { cost: Amount }

            behavior classify : (cost: Amount) -> Submitted | Waiting
                constructs Submitted, Waiting

            let classify (cost) = {
                guard cost.value <= 100 else Waiting { cost = cost }
                Submitted { cost = cost }
            }

            behavior submit : (request: Draft) -> Submitted | Waiting

            let submit (request) = classify(request.cost)

            example classify
                | "cheap" : (Amount(50)) -> Submitted { cost = Amount(50) }

            example submit
                | "dear" : (Draft { cost = Amount(200) }) -> Submitted { cost = Amount(200) }
            """;

    /**
     * An arm of one behavior only another behavior's row that does not hold goes through is marked
     * under the first, with the row named as the second's — in a page narrowed to the first too.
     *
     * <p>The row is not the first's, so it is not among the rows that page says do not hold; what
     * says so at the foot is the count, and a row of the first's own through the same arm takes the
     * mark away.
     */
    @Test
    void anArmOnlyAnotherBehaviorsRowThatDoesNotHoldGoesThroughIsMarked() {
        String narrowed = human(THROUGH, "classify");
        assertTrue(narrowed.contains("      ~ only a row that does not hold goes through `else`"
                + " (14:5): submit dear (26:7)\n"), narrowed);
        assertFalse(narrowed.contains("row does not hold:"), narrowed);
        assertTrue(narrowed.endsWith("1 obligation counted as met is covered only by rows that do"
                + " not hold, marked `~`.\n"), narrowed);

        String withAnother = THROUGH.replace(
                "    | \"cheap\" : (Amount(50)) -> Submitted { cost = Amount(50) }\n",
                "    | \"cheap\" : (Amount(50)) -> Submitted { cost = Amount(50) }\n"
                        + "    | \"dear\" : (Amount(200)) -> Waiting { cost = Amount(200) }\n");
        assertFalse(human(withAnother, "classify").contains(
                "~ only a row that does not hold goes through `else`"), withAnother);
    }

    /** A helper read under both arms of a body, so each of its arms is one arm at two places. */
    private static final String TWICE = """
            module example.equalanswers

            data On
            data Off
            data Flag = On | Off

            data Safe
            data Risky
            data Mode = Safe | Risky

            data X
            data Y
            data Z
            data Answer = X | Y | Z

            let choose (flag: Flag, yes: Answer, no: Answer): Answer =
                match flag with
                    | On  -> yes
                    | Off -> no

            behavior decide : (mode: Mode, flag: Flag) -> Answer

            let decide (mode, flag) =
                match mode with
                    | Safe  -> choose(flag, X, X)
                    | Risky -> choose(flag, Y, Z)

            example decide
                | "safe on"   : (Safe, On)   -> X
                | "risky on"  : (Risky, On)  -> Y
                | "risky off" : (Risky, Off) -> Y
            """;

    /**
     * An arm written once and reached at two places is one arm, and a row through either place is
     * a row through it.
     *
     * <p>The row that does not hold goes through `Off` under `Risky`; a row that holds through `Off`
     * under `Safe` is another row through the same arm, and takes the mark away.
     */
    @Test
    void anArmReachedAtTwoPlacesIsCoveredByARowThroughEither() {
        String human = human(TWICE);
        assertTrue(human.contains("~ only a row that does not hold goes through `case Off`"),
                human);
        String withAnother = TWICE + "    | \"safe off\"  : (Safe, Off)  -> X\n";
        assertFalse(human(withAnother).contains(
                "~ only a row that does not hold goes through `case Off`"), withAnother);
    }

    /** A type whose line is owed by its declaration, and one behavior's row is all that stands at
     *  its boundary — a row that does not hold. */
    private static final String CARRIED = """
            module example.carried

            data UserId = String
                invariant nonempty = String.length(value) >= 1

            data Draft = { owner: UserId }
            data Task = { owner: UserId }

            data Ok
            data No

            behavior schedule : (d: Draft) -> Ok | No
            let schedule (d) = Ok

            behavior touch : (t: Task) -> Ok
            let touch (t) = Ok

            example schedule
                | "at the boundary" : (Draft { owner = UserId("x") }) -> No

            example touch
                | "well inside" : (Task { owner = UserId("abcd") }) -> Ok
            """;

    /**
     * A report narrowed to a behavior whose own rows all hold still says that something it is
     * shown rests on a row that does not.
     *
     * <p>The row is another behavior's, so it is not in the narrowed report's list of rows that do
     * not hold; and the line under the declaration is, because the type is one this behavior
     * carries. Without the count after the verdict, the narrowed report would end on `satisfied`
     * over a point only a row that does not hold stands at.
     */
    @Test
    void aReportNarrowedToAnotherBehaviorStillCountsWhatRestsOnTheRow() {
        String human = human(CARRIED, "touch");
        assertFalse(human.contains("row does not hold:"), human);
        assertTrue(human.contains("~ only a row that does not hold is at the ON point"),
                human);
        assertTrue(human.contains("schedule at the boundary (0:19:7)"), human);
        assertTrue(human.endsWith("1 obligation counted as met is covered only by rows that do"
                + " not hold, marked `~`.\n"), human);
    }

    /**
     * A row of another behavior at the same point is another row, whichever reading it was read at.
     *
     * <p>The line is owed once and read once per behavior carrying the type, so the row that does
     * not hold and the row that does are found by two readings of it. What the point rests on is
     * what those readings found together.
     */
    @Test
    void aRowAtTheSamePointThroughAnotherReadingIsAnotherRow() {
        String human = human(CARRIED.replace("UserId(\"abcd\")", "UserId(\"y\")"));
        assertFalse(human.contains("~ only a row that does not hold is at the ON point"), human);
        assertTrue(human.contains("1 row does not hold:"), human);
    }

    /** {@code model} compiled, with every measure asked for and its rows run. */
    private static Compilation measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static String human(String model) {
        return human(model, null);
    }

    /**
     * The page, narrowed to {@code behavior} where one is named, and held to its own closing line:
     * the number of lines it says it marked `~` is the number it marked.
     */
    private static String human(String model, String behavior) {
        Compilation compilation = measured(model);
        AdequacyReport report = AdequacyReport.of(compilation);
        String human = (behavior == null ? report : report.only(null, behavior))
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        Matcher said = LEGEND.matcher(human);
        assertEquals(marked(human).size(), said.find() ? Integer.parseInt(said.group(1)) : 0,
                () -> "the page counts the marks it wrote: " + human);
        return human;
    }

    private static final Pattern LEGEND = Pattern.compile(
            "(\\d+) obligations? counted as met (?:is|are) covered only by rows that do not hold");

    private static JsonNode json(String model) {
        Compilation compilation = measured(model);
        return JsonMapper.builder().build().readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
    }

    /** The lines of a page marked `~`, in the order it prints them. */
    private static List<String> marked(String human) {
        return human.lines().filter(line -> line.stripLeading().startsWith("~ ")).toList();
    }

    private static JsonNode behavior(JsonNode root, String name) {
        for (JsonNode module : root.get("modules")) {
            for (JsonNode behavior : module.get("behaviors")) {
                if (behavior.get("name").asString().equals(name)) {
                    return behavior;
                }
            }
        }
        throw new AssertionError("no behavior `" + name + "` in " + root);
    }

    /** Every `onlyWitnessedBy` array the document writes, wherever it is. */
    private static List<JsonNode> onlyWitnessedBy(JsonNode root) {
        List<JsonNode> out = new ArrayList<>();
        collect(root, out);
        return out;
    }

    private static int onlyWitnessedByIn(JsonNode node) {
        return onlyWitnessedBy(node).size();
    }

    private static void collect(JsonNode node, List<JsonNode> out) {
        if (node.isObject()) {
            for (String key : node.propertyNames()) {
                if (key.equals("onlyWitnessedBy")) {
                    out.add(node.get(key));
                } else {
                    collect(node.get(key), out);
                }
            }
        } else if (node.isArray()) {
            for (JsonNode each : node) {
                collect(each, out);
            }
        }
    }
}
