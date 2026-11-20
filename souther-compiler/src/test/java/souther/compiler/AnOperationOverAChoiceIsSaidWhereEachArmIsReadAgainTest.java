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
 * An operation written over a choice, outside it, is worked out on each arm with the arm's answer,
 * and a comparison read again with each arm taken keeps what it works out there. Where it may
 * pass an {@code Int} it is told on the arm whose answer takes it there, and no reader says a run
 * may stop where nothing here says, whatever the shape of the operation: a number added to the
 * choice, held against what it chose so that the arm's comparison holds on every row, or summed
 * with the choice in a list. Chosen only below a hundred, no arm passes the type: nothing is told,
 * and nothing is said to be untold.
 */
class AnOperationOverAChoiceIsSaidWhereEachArmIsReadAgainTest {

    private static final String PAST = "(if q > 0 then q else 0)";

    private static final String WITHIN = "(if q > 0 && q < 100 then q else 0)";

    private static final Map<String, String> FORMS = new LinkedHashMap<>();

    private static final Map<String, String> EXPECTED = new LinkedHashMap<>();

    private static void form(String name, String condition, String said) {
        FORMS.put(name, condition);
        EXPECTED.put(name, said);
    }

    static {
        form("aNumberAdded", PAST + " + 1 >= 5", "told true, untold 0");
        form("aNumberAddedWithinTheType", WITHIN + " + 1 >= 5", "told false, untold 0");
        form("aNumberAddedHeldAgainstTheChosen", PAST + " + 1 >= q", "told true, untold 0");
        form("summedWithANumber", "List.sum([" + PAST + ", 1]) >= q", "told true, untold 0");
    }

    @Test
    void anOperationOverAChoiceIsToldWhereAnArmPassesTheTypeAndLeftUntoldNowhere() {
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
