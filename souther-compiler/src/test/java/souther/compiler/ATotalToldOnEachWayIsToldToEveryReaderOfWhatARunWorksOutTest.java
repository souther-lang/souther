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
 * A total whose stop the rule that read it says on each way of keeping its elements is said so to
 * every reader of what a run works out, and not only to the reading that stopped at it: the
 * evaluation of the answer of an arm, the condition of a choice, and the quotient a mean is.
 *
 * <p>Each form is written twice. Keeping {@code q} where it is above nought, a way keeps two of
 * it and a run may pass an {@code Int} there: the stop is told, and no reader says a run may stop
 * where nothing here says. Keeping it only where it is below a hundred, no way a run takes passes
 * the type: nothing is told, and nothing is said to be untold. A reader that told the stop on
 * rows no way it is worked out on reaches, or said it untold where it is said on the ways, is
 * found by one of the two; one that told nothing, or everything, by the other.
 *
 * <p>Each is held against the same total written as choices, which the rule reads way by way,
 * so that a reader that asks only one of the two readings is found. What a mean divides by is
 * no stop told here: the quotient is read as answering where the count is not nought, and the
 * rows are kept to that.
 */
class ATotalToldOnEachWayIsToldToEveryReaderOfWhatARunWorksOutTest {

    private static final Map<String, String> FORMS = new LinkedHashMap<>();

    private static final Map<String, String> EXPECTED = new LinkedHashMap<>();

    static {
        for (Map.Entry<String, String> kept : Map.of("past the type", "x > 0",
                "within the type", "x > 0 && x < 100").entrySet()) {
            String filtered = "List.sum(List.filter(x -> " + kept.getValue() + ", [q, q]))";
            String chosen = "List.sum(List.map(x -> if " + kept.getValue()
                    + " then x else 0, [q, q]))";
            String said = kept.getKey().equals("past the type") ? "told true, untold 0"
                    : "told false, untold 0";
            for (Map.Entry<String, String> total : Map.of("filtered", filtered, "chosen", chosen)
                    .entrySet()) {
                String suffix = " " + total.getKey() + " " + kept.getKey();
                FORMS.put("theAnswerOfAnArm" + suffix,
                        "(if q > 3 then " + total.getValue() + " else 0) >= 10");
                FORMS.put("theConditionOfAChoice" + suffix,
                        "(if " + total.getValue() + " > 5 then 1 else 2) >= 2");
                FORMS.put("aMean" + suffix, total.getValue() + " / List.length(List.filter(x -> "
                        + kept.getValue() + ", [q, q])) >= 10");
            }
            FORMS.keySet().stream().filter(name -> name.endsWith(kept.getKey()))
                    .forEach(name -> EXPECTED.put(name, said));
        }
    }

    @Test
    void everyReaderTellsTheStopWhereAWayPassesTheTypeAndLeavesNoneUntold() {
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
        Map<String, int[]> notes = notes(report);
        for (int at = 0; at < names.size(); at++) {
            int[] counts = notes.getOrDefault("b" + at, new int[2]);
            said.put(names.get(at), "told " + (counts[0] > 0) + ", untold " + counts[1]);
        }
        assertEquals(EXPECTED, said, report);
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
