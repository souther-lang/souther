package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line a helper draws is one line however many calls read it, and so is each line beside it.
 *
 * <p>{@code atLeast} is called in both arms of {@code flag}, so the line it draws is read twice, and
 * the rows that took each arm reach one reading of it. A line beside it is a fault in the helper,
 * one threshold at both calls: it stands only where one threshold keeps and refuses what the rows
 * of both arms have the model keep and refuse. So one arm's rows ruling it out rule it out, and two
 * arms whose rows each leave it standing, at thresholds no one threshold reaches, rule it out
 * together. Where it stands, the input named is a step from one arm's rows along that arm's way.
 */
class ALineBesideOneIsNamedForTheLineAndNotForOneReadingOfItTest {

    private static final String ON_THE_ENTRY = """
            module p
            let atLeast (a: Int, b: Int): Bool = a >= b
            behavior f : (by: Map<String, Int>, k: String, q: Int, flag: Bool) -> Int
            let f (by, k, q, flag) =
                match Map.get(k, by) with
                    | None -> 0
                    | Some got -> if flag then (if atLeast(got, q) then 1 else 2)
                        else (if atLeast(got, q) then 3 else 4)
            example f
                | "on" : ([("Q", 5)], "Q", 5, true) -> 1
                | "off" : ([("Q", 4)], "Q", 5, true) -> 2
                | "in" : ([("Q", 9)], "Q", 5, true) -> 1
                | "out" : ([("Q", 0)], "Q", 5, true) -> 2
            """;

    private static final String RULED_OUT_AT_ONE = """
                | "kept higher" : ([("Q", 7)], "Q", 7, true) -> 1
                | "kept lower" : ([("Q", 3)], "Q", 2, true) -> 1
                | "refused higher" : ([("Q", 10)], "Q", 12, true) -> 2
                | "refused lower" : ([("Q", -1)], "Q", 0, true) -> 2
                | "on, the other way" : ([("Q", 5)], "Q", 5, false) -> 3
                | "off, the other way" : ([("Q", 4)], "Q", 5, false) -> 4
                | "in, the other way" : ([("Q", 9)], "Q", 5, false) -> 3
                | "out, the other way" : ([("Q", 0)], "Q", 5, false) -> 4
                | "none" : ([], "Q", 5, true) -> 0
            """;

    /**
     * The other arm's rows at the next threshold along. The line weighing the entry twice is left
     * standing by both arms at thresholds the two share; the other two lines are left by each arm
     * at thresholds the other's rows refuse.
     */
    private static final String AT_THE_NEXT_THRESHOLD = """
                | "on, the other way" : ([("Q", 6)], "Q", 6, false) -> 3
                | "off, the other way" : ([("Q", 5)], "Q", 6, false) -> 4
                | "in, the other way" : ([("Q", 10)], "Q", 6, false) -> 3
                | "out, the other way" : ([("Q", 1)], "Q", 6, false) -> 4
                | "none" : ([], "Q", 5, true) -> 0
            """;

    /** The same, with no lookup on the way: each reading names an input from the rows alone. */
    private static final String ON_THE_INPUT = """
            module p
            let atLeast (a: Int, b: Int): Bool = a >= b
            behavior f : (x: Int, q: Int, flag: Bool) -> Int
            let f (x, q, flag) =
                if flag then (if atLeast(x, q) then 1 else 2) else (if atLeast(x, q) then 3 else 4)
            example f
                | "on" : (5, 5, true) -> 1
                | "off" : (4, 5, true) -> 2
                | "in" : (9, 5, true) -> 1
                | "out" : (0, 5, true) -> 2
                | "kept higher" : (7, 7, true) -> 1
                | "kept lower" : (3, 2, true) -> 1
                | "refused higher" : (10, 12, true) -> 2
                | "refused lower" : (-1, 0, true) -> 2
                | "on, the other way" : (5, 5, false) -> 3
                | "off, the other way" : (4, 5, false) -> 4
                | "in, the other way" : (9, 5, false) -> 3
                | "out, the other way" : (0, 5, false) -> 4
            """;

    /** Each call's rows on the line at a threshold of its own: five at one, ten at the other. */
    private static final String AT_TWO_THRESHOLDS = """
            module p
            let atLeast (a: Int, b: Int): Bool = a >= b
            behavior f : (x: Int, q: Int, flag: Bool) -> Int
            let f (x, q, flag) =
                if flag then (if atLeast(x, q) then 1 else 2) else (if atLeast(x, q) then 3 else 4)
            example f
                | "on" : (5, 5, true) -> 1
                | "off" : (4, 5, true) -> 2
                | "in" : (9, 5, true) -> 1
                | "out" : (0, 5, true) -> 2
                | "on, the other way" : (10, 10, false) -> 3
                | "off, the other way" : (9, 10, false) -> 4
                | "in, the other way" : (14, 10, false) -> 3
                | "out, the other way" : (5, 10, false) -> 4
            """;

    /**
     * A line beside the helper's is one threshold at both calls. Each call's rows alone leave every
     * line of the family standing, each at its own place; no one threshold keeps and refuses what
     * both calls' rows have the model keep and refuse, so together they rule every one of them out.
     */
    @Test
    void rowsAtTwoCallsRuleOutTheLinesNeitherCallsRowsRuleOutAlone() {
        String alone = ON_THE_INPUT.lines().filter(line -> !line.contains("higher")
                        && !line.contains("lower") && !line.contains("the other way"))
                .reduce("", (text, line) -> text + line + "\n");
        assertFalse(besides(report(alone)).isEmpty(), "one call's rows leave the lines standing");

        assertEquals(List.of(), besides(report(AT_TWO_THRESHOLDS)));
    }

    /** The same of a helper that singles a value out: two calls whose rows put the value at two
     *  places along each line beside it rule each one out. */
    @Test
    void rowsAtTwoCallsPuttingAValueAtTwoPlacesRuleTheLinesOut() {
        String singled = """
                module p
                let same (a: Int, b: Int): Bool = a == b
                behavior f : (x: Int, q: Int, flag: Bool) -> Int
                let f (x, q, flag) =
                    if flag then (if same(x, q) then 1 else 2) else (if same(x, q) then 3 else 4)
                example f
                    | "on" : (5, 5, true) -> 1
                    | "below" : (4, 5, true) -> 2
                    | "above" : (6, 5, true) -> 2
                    | "far below" : (0, 5, true) -> 2
                    | "far above" : (9, 5, true) -> 2
                """;
        assertFalse(besides(report(singled)).isEmpty(), "one call's rows leave the lines standing");

        assertEquals(List.of(), besides(report(singled + """
                    | "on, the other way" : (10, 10, false) -> 3
                    | "below, the other way" : (9, 10, false) -> 4
                    | "above, the other way" : (11, 10, false) -> 4
                    | "far below, the other way" : (5, 10, false) -> 4
                    | "far above, the other way" : (14, 10, false) -> 4
                """)));
    }

    private static String report(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static List<String> besides(String report) {
        return report.lines().map(String::strip)
                .filter(line -> line.startsWith("! no row tells")).toList();
    }

    /** Rows ruling the lines out at one call settle them for the line, past a lookup where nothing
     *  showed an input arriving at the other. */
    @Test
    void theRowsRulingTheLinesOutAtOneCallSettleThemPastALookup() {
        assertTrue(besides(report(ON_THE_ENTRY + RULED_OUT_AT_ONE)).isEmpty());
    }

    /** And where the other call's rows leave them standing with an input named from the rows
     *  alone: one reading ruling a line out and another leaving it are two calls' rows, and the
     *  line is ruled out. */
    @Test
    void theRowsRulingTheLinesOutAtOneCallSettleThemWhereTheOtherLeavesThem() {
        assertTrue(besides(report(ON_THE_INPUT)).isEmpty());
    }

    /**
     * Two calls whose rows leave a line standing at thresholds they share, past a lookup: that
     * line is named, at a place both arms' rows leave it and an input answering it and the model
     * differently there, and the lines no one threshold leaves standing at both are not. Written
     * down, the row named rules its line out.
     */
    @Test
    void aLineBothCallsLeaveStandingIsNamedAtAnInputThatRulesItOut() {
        String model = ON_THE_ENTRY + AT_THE_NEXT_THRESHOLD;
        List<String> standing = besides(report(model));
        List<Named> named = named(standing);
        assertEquals(1, standing.size(), () -> report(model));
        assertEquals(1, named.size(), () -> report(model));
        assertTrue(named.getFirst().line().startsWith("2 * by[*] - q = "), () -> report(model));

        StringBuilder written = new StringBuilder(model);
        for (Named one : named) {
            boolean modelKeeps = one.entry() >= one.q();
            boolean lineKeeps = one.byWeight() * one.entry() + one.qWeight() * one.q() >= one.at();
            assertNotEquals(modelKeeps, lineKeeps, one::toString);
            written.append("    | \"named for ").append(one.line()).append("\" : ([(\"Q\", ")
                    .append(one.entry()).append(")], \"Q\", ").append(one.q()).append(", true) -> ")
                    .append(modelKeeps ? 1 : 2).append('\n');
        }
        List<String> left = besides(report(written.toString()));
        for (Named one : named) {
            assertTrue(left.stream().noneMatch(line -> line.contains("from `" + one.line() + "`")),
                    () -> one + " is left after its row was written: " + left);
        }
    }

    /**
     * One line named beside the helper's: the line as written, its weights and place, and the
     * input named — the entry and the threshold.
     */
    private record Named(String line, long byWeight, long qWeight, long at, long entry, long q) {}

    private static final Pattern NAMED = Pattern.compile(
            "from `(.+) = (-?\\d+)`, and a row at `by\\[\\*] = (-?\\d+), q = (-?\\d+)` would");

    private static final Pattern TERM = Pattern.compile("(-)?\\s*(?:(\\d+) \\* )?(by\\[\\*]|q)");

    /** Each line named with an input, as {@link Named}. */
    private static List<Named> named(List<String> besides) {
        List<Named> out = new ArrayList<>();
        for (String line : besides) {
            Matcher matched = NAMED.matcher(line);
            if (!matched.find()) {
                continue;
            }
            long by = 0;
            long q = 0;
            Matcher term = TERM.matcher(matched.group(1));
            while (term.find()) {
                long weight = (term.group(1) == null ? 1 : -1)
                        * (term.group(2) == null ? 1 : Long.parseLong(term.group(2)));
                if (term.group(3).equals("q")) {
                    q = weight;
                } else {
                    by = weight;
                }
            }
            long entry = Long.parseLong(matched.group(3));
            long threshold = Long.parseLong(matched.group(4));
            long at = Long.parseLong(matched.group(2));
            out.add(new Named(matched.group(1) + " = " + at, by, q, at, entry, threshold));
        }
        return out;
    }
}
