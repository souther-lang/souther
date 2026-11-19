package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A total whose stop the rule that read it tells on each way of keeping its elements is told so to
 * every reader of what a run works out, and not only to the reading that stopped at it: the
 * evaluation of the answer of an arm, the condition of a choice, and the quotient a mean is. Each
 * comparison below may stop a run where two of {@code q} pass an {@code Int}, and is told so and
 * nothing else: no reader says a run may stop where nothing here says.
 *
 * <p>Each form is held against the same total written as choices, which the rule reads way by
 * way, so that a reader that asks only one of the two readings is found.
 */
class ATotalToldOnEachWayIsToldToEveryReaderOfWhatARunWorksOutTest {

    private static final String FILTERED = "List.sum(List.filter(x -> x > 0, [q, q]))";

    private static final String CHOSEN = "List.sum(List.map(x -> if x > 0 then x else 0, [q, q]))";

    private static final Map<String, String> FORMS = new LinkedHashMap<>();

    static {
        for (Map.Entry<String, String> total : Map.of("filtered", FILTERED, "chosen", CHOSEN)
                .entrySet()) {
            FORMS.put("theAnswerOfAnArm " + total.getKey(),
                    "(if q > 3 then " + total.getValue() + " else 0) >= 10");
            FORMS.put("theConditionOfAChoice " + total.getKey(),
                    "(if " + total.getValue() + " > 5 then 1 else 2) >= 2");
        }
        FORMS.put("aMean filtered", FILTERED + " / List.length(List.filter(x -> x > 0, [q, q]))"
                + " >= 10");
    }

    @Test
    void everyReaderTellsTheStopAndLeavesNoneUntold() {
        List<String> names = new ArrayList<>(FORMS.keySet());
        StringBuilder model = new StringBuilder(
                "module demo\n\ndata In = { q: Int }\ndata Out = Int\n");
        for (int at = 0; at < names.size(); at++) {
            model.append("\nbehavior b").append(at)
                    .append(" : (i: In) -> Out constructs Out\nlet b").append(at)
                    .append(" (i) = Out { value = if ")
                    .append(FORMS.get(names.get(at)).replaceAll("\\bq\\b", "i.q"))
                    .append(" then 1 else 2 }\n");
        }
        Compilation compilation = ACompiledModel.measured(model.toString(),
                new Adequacy.Asked(Adequacy.Level.OFF, false));
        String report = AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
        Map<String, String> said = new LinkedHashMap<>();
        Map<String, String> expected = new LinkedHashMap<>();
        Map<String, int[]> notes = notes(report);
        for (int at = 0; at < names.size(); at++) {
            int[] counts = notes.getOrDefault("b" + at, new int[2]);
            said.put(names.get(at), "told " + (counts[0] > 0) + ", untold " + counts[1]);
            expected.put(names.get(at), "told true, untold 0");
        }
        assertEquals(expected, said, report);
    }

    /** How many {@code may stop a run} notes, and how many said to stop where nothing says, each
     *  behavior's report holds. */
    private static Map<String, int[]> notes(String report) {
        Pattern header = Pattern.compile("^(\\w+)\\s+implemented\\b.*");
        Map<String, int[]> out = new LinkedHashMap<>();
        String current = null;
        for (String line : report.lines().map(String::strip).toList()) {
            Matcher started = header.matcher(line);
            if (started.matches()) {
                current = started.group(1);
                out.put(current, new int[2]);
            } else if (current != null && line.contains("may stop a run")) {
                out.get(current)[0]++;
            } else if (current != null && line.startsWith("· not read:")
                    && line.contains(UnreadBesideItsStops.STOPS_NOT_ALL_TOLD)) {
                out.get(current)[1]++;
            }
        }
        return out;
    }
}
