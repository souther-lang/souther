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
 * evaluation of the answer of an arm, the condition of a choice read under a rule of its own, and
 * the quotient a mean is. Kept where {@code q} is above nought, a way keeps two of it and a run
 * may pass an {@code Int} there: the stop is told, and no reader says a run may stop where nothing
 * here says.
 *
 * <p>Kept only below a hundred, no way a run takes passes the type, and nothing is told: a stop
 * said on rows wider than the way's is found there, both where the total is read once for every
 * way and where it is read way by way, whose count splits inside each way. What a mean divides by
 * is no stop told here: the quotient is read as answering where the count is not nought.
 */
class ATotalToldOnEachWayIsToldToEveryReaderOfWhatARunWorksOutTest {

    private static final String PAST = "x > 0";

    private static final String WITHIN = "x > 0 && x < 100";

    private static final Map<String, String> FORMS = new LinkedHashMap<>();

    private static final Map<String, String> EXPECTED = new LinkedHashMap<>();

    private static String filtered(String kept) {
        return "List.sum(List.filter(x -> " + kept + ", [q, q]))";
    }

    private static String meanOf(String total, String kept) {
        return total + " / List.length(List.filter(x -> " + kept + ", [q, q])) >= 10";
    }

    private static void form(String name, String condition, String said) {
        FORMS.put(name, condition);
        EXPECTED.put(name, said);
    }

    static {
        form("theAnswerOfAnArm", "(if q > 3 then " + filtered(PAST) + " else 0) >= 10",
                "told true, untold 0");
        form("theConditionOfAChoice", "(if " + filtered(PAST) + " > 5 then 1 else 2) >= 2",
                "told true, untold 0");
        form("aMean", meanOf(filtered(PAST), PAST), "told true, untold 0");
        form("aMeanWithinTheType", meanOf(filtered(WITHIN), WITHIN), "told false, untold 0");
        form("aMeanOfChoicesWithinTheType", meanOf("List.sum(List.map(x -> if " + WITHIN
                + " then x else 0, [q, q]))", WITHIN), "told false, untold 0");
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
