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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row that does not hold is counted where it went, and a report says what only such rows cover.
 *
 * <p>The count is not what changes. A row that ran went through what it went through, so an arm, a
 * class, a point or a rule it reached is met. What a reader is owed beside that number is which of
 * those they lose by correcting or deleting the row — and that is where nothing else covers them,
 * which is a different set from where the row went.
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
                        + " (comparison@5:28): label `24 is warm` (9:7)"),
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
                                + " label `24 is warm` (9:7)",
                        "      ~ only a row that does not hold is at the OFF point"
                                + " (comparison@5:28): label `24 is warm` (9:7)",
                        "      ~ only a row that does not hold goes through `else` (5:17):"
                                + " label `24 is warm` (9:7)",
                        "      ~ only a row that does not hold takes a decision rule:"
                                + " label `24 is warm` (9:7)"),
                marked(human), human);
    }

    /**
     * The report ends on the rows that do not hold, whatever the verdict above them says.
     *
     * <p>The verdict is unchanged: it answers whether the rows cover what the model owes, and a
     * row that does not hold covers what it went through. Said after it, because the last lines
     * are what a terminal or a build log leaves in front of a reader.
     */
    @Test
    void theReportEndsOnTheRowsThatDoNotHold() {
        String human = human(FAILING);
        assertTrue(human.endsWith("""
                adequacy: satisfied
                1 row does not hold:
                  label `24 is warm` (0:9:7)
                1 obligation counted as met is covered only by rows that do not hold, marked `~`.
                """), human);
    }

    /** And a report whose rows all hold says nothing of the kind. */
    @Test
    void rowsThatAllHoldAddNothing() {
        String human = human(HOLDING);
        assertEquals(List.of(), marked(human), human);
        assertFalse(human.contains("does not hold"), human);
        assertTrue(human.endsWith("adequacy: satisfied\n"), human);

        JsonNode label = behavior(json(HOLDING), "label");
        assertEquals(0, label.get("rowsThatDoNotHold").size(), label::toString);
        assertEquals(List.of(), onlyWitnessedBy(json(HOLDING)));
    }

    /** Two rows that do not hold through one arm are both named, in the order they were read. */
    @Test
    void everyRowThatDoesNotHoldIsNamed() {
        String human = human(ONLY.replace("    | \"10 is cold\" : (Celsius(10)) -> Cold\n",
                "    | \"25 is warm\" : (Celsius(25)) -> Cold\n"));
        assertTrue(human.contains("      ~ only rows that do not hold go through `else` (5:17):"
                        + " label `24 is warm` (9:7), label `25 is warm` (10:7)\n"),
                human);
    }

    /**
     * A row waiting for its answer is another row, and the point it stands at rests on more than
     * the row that does not hold.
     *
     * <p>What the mark says is that correcting the row takes the point out of the count. A row
     * whose answer is owed keeps it there, whatever it will be found to answer.
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
        // One per measure the page marks, and every one of them the same row.
        List<JsonNode> named = onlyWitnessedBy(root);
        assertEquals(4, named.size(), named::toString);
        for (JsonNode rows : named) {
            assertEquals(1, rows.size(), rows::toString);
            assertEquals(failing.get(0), rows.get(0), rows::toString);
        }
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
        Compilation compilation = measured(CARRIED);
        String human = AdequacyReport.of(compilation).only(null, "touch")
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertFalse(human.contains("row does not hold:"), human);
        assertTrue(human.contains("~ only a row that does not hold is at the ON point"),
                human);
        assertTrue(human.contains("schedule `at the boundary` (0:19:7)"), human);
        assertTrue(human.endsWith("1 obligation counted as met is covered only by rows that do"
                + " not hold, marked `~`.\n"), human);
    }

    /** {@code model} compiled, with every measure asked for and its rows run. */
    private static Compilation measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
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

    private static String human(String model) {
        Compilation compilation = measured(model);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

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
