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
 * A line a helper draws is one line however many calls read it, and the rows each call reads are
 * the rows that reached it.
 *
 * <p>{@code atLeast} is called in both arms of {@code flag}, so the line it draws is read twice, and
 * each reading folds the rows that took its arm. One reading's rows can rule a line beside it out
 * where the other's leave it — the line is then ruled out, since a row telling the two apart at
 * either call shows which line the model draws. Two readings can leave it at two places; where a
 * row is named for it, the place said is the reading's whose search composed that row, and the row
 * is that reading's row read back.
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

    /** The other arm's rows at another threshold, which leave the lines at other places. */
    private static final String LEFT_ELSEWHERE_AT_THE_OTHER = """
                | "on, the other way" : ([("Q", 10)], "Q", 10, false) -> 3
                | "off, the other way" : ([("Q", 9)], "Q", 10, false) -> 4
                | "in, the other way" : ([("Q", 14)], "Q", 10, false) -> 3
                | "out, the other way" : ([("Q", 5)], "Q", 10, false) -> 4
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
     * Two calls whose rows leave the lines at two places: each line is named at a place and an
     * input, and the input is a row answering the two lines differently at that place — the
     * reading's own pair, and not one reading's place beside another's row. Written down, the row
     * named rules its line out.
     */
    @Test
    void aLineIsNamedAtThePlaceTheReadingThatNamedItLeftItAt() {
        String model = ON_THE_ENTRY + LEFT_ELSEWHERE_AT_THE_OTHER;
        List<Named> named = named(besides(report(model)));
        assertFalse(named.isEmpty(), () -> report(model));

        StringBuilder written = new StringBuilder(model);
        for (Named one : named) {
            boolean modelKeeps = one.entry() >= one.q();
            boolean lineKeeps = one.byWeight() * one.entry() + one.qWeight() * one.q() >= one.at();
            assertNotEquals(modelKeeps, lineKeeps, one::toString);
            written.append("    | \"named for ").append(one.line()).append("\" : ([(\"Q\", ")
                    .append(one.entry()).append(")], \"Q\", ").append(one.q()).append(", ")
                    .append(one.flag()).append(") -> ").append(answer(one)).append('\n');
        }
        List<String> left = besides(report(written.toString()));
        for (Named one : named) {
            assertTrue(left.stream().noneMatch(line -> line.contains("from `" + one.line() + "`")),
                    () -> one + " is left after its row was written: " + left);
        }
    }

    /** The answer of the arm the named row is written for. */
    private static int answer(Named one) {
        boolean holds = one.entry() >= one.q();
        return one.flag() ? (holds ? 1 : 2) : (holds ? 3 : 4);
    }

    /**
     * One line named beside the helper's: the line as written, its weights and place, and the
     * input named — the entry and the threshold — with the arm whose reading named it, which is the
     * arm the row is written in.
     */
    private record Named(String line, long byWeight, long qWeight, long at, long entry, long q,
                         boolean flag) {}

    private static final Pattern NAMED = Pattern.compile(
            "from `(.+) = (-?\\d+)`, and a row at `by\\[\\*] = (-?\\d+), q = (-?\\d+)` would");

    private static final Pattern TERM = Pattern.compile("(-)?\\s*(?:(\\d+) \\* )?(by\\[\\*]|q)");

    /** Each line named, as {@link Named}: its arm is the one whose rows stand at its threshold. */
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
            // The arm whose rows hold the threshold of the line's place: five for one, ten for the
            // other, read off where each arm's rows on the model's line stand along it.
            long at = Long.parseLong(matched.group(2));
            boolean flag = at == by * 5 + q * 5;
            out.add(new Named(matched.group(1) + " = " + at, by, q, at, entry, threshold, flag));
        }
        return out;
    }
}
