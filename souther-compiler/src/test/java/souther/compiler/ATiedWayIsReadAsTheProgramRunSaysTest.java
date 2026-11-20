package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.runtime.ConstraintViolation;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the report reads of two numbers a way ties, held to the program run.
 *
 * <p>The truth is the program: each form is a way and a comparison after it, compiled and run on
 * every pair of numbers of a small box, and the answer says whether the way is passed and, if it
 * is, how the comparison comes out. So for each value of a number the program shows whether the
 * way is passed at every other value or at some, and whether the comparison comes out true at
 * every row that gets to it or at some. What the report says is the classes of each number, cut
 * where the compiler read a line, and where it reads the form it is held to this: a class holds
 * no two values the program tells apart. A line the program draws that the report does not is a
 * class holding two values it tells apart, so that is the one direction asked; a line the report
 * draws and the program does not is no wrong class, only a finer one.
 *
 * <p>A form the report does not read is not held to anything, and what a reader says of the rows
 * of a way rests on a list of what bears on them that it can add to and the program cannot: so the
 * forms are asked of the program and not of whoever wrote the reading. A form is added here when
 * a reading of rows is changed; what the program says is what a reading is checked against.
 */
class ATiedWayIsReadAsTheProgramRunSaysTest {

    private static final int TOP = 12;

    /** A way, and a comparison after it, on {@code e} and {@code p}: {@code e} runs from nought
     *  to twelve, {@code p} from one. */
    private static final Map<String, String[]> FORMS = new LinkedHashMap<>();

    static {
        // One for each way the ties come: a coefficient that rounds in twos, a sum with whole
        // steps, and one that rounds in threes.
        FORMS.put("aLineAndTheDoubleOfAnother", new String[] {"e >= p", "e < 2 * p"});
        FORMS.put("aSumHeldBelowAndTheOrder", new String[] {"e + p <= 12", "e < p"});
        FORMS.put("aTripleOfAnother", new String[] {"e >= p", "e < 3 * p"});
    }

    private static final Pattern CLASS = Pattern.compile(
            "^[^:]+: (-?\\d+) (<=|<) x (<=|<) (-?\\d+)$");

    @Test
    void whatTheReportReadsOfTwoTiedNumbersIsWhatTheProgramRunSays() throws Exception {
        List<String> names = new ArrayList<>(FORMS.keySet());
        StringBuilder model = new StringBuilder("module demo\n\n"
                + "data Eaches = Int\n    invariant value >= 0 && value <= " + TOP + "\n"
                + "data PackSize = Int\n    invariant value >= 1 && value <= " + TOP + "\n"
                + "data In = { e: Eaches, p: PackSize }\ndata Out = Int\n");
        for (int at = 0; at < names.size(); at++) {
            String[] form = FORMS.get(names.get(at));
            model.append("\nbehavior b").append(at).append(" : (i: In) -> Out\nlet b").append(at)
                    .append(" (i) = Out { value = if ").append(written(form[0]))
                    .append(" then (if ").append(written(form[1])).append(" then 1 else 2)")
                    .append(" else 3 }\n");
        }
        Compilation compilation = ACompiledModel.measured(model.toString(),
                Adequacy.Asked.fullReport());
        JsonNode report = JsonMapper.builder().build().readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(model.toString()),
                ATiedWayIsReadAsTheProgramRunSaysTest.class.getClassLoader());
        TreeSet<String> read = new TreeSet<>();
        for (int at = 0; at < names.size(); at++) {
            JsonNode behavior = behaviorNamed(report, "b" + at);
            if (!isRead(behavior)) {
                continue;
            }
            read.add(names.get(at));
            int[][] outcomes = outcomes(loader, at);
            for (String axis : List.of("i.e", "i.p")) {
                heldToTheProgram(names.get(at), axis, classesOf(behavior, axis), outcomes);
            }
        }
        // That the report reads a form is what holds it to the program, so each of these is read:
        // a form no longer read is a reading lost, and agreement on none is none.
        assertEquals(new TreeSet<>(names), read, "forms read");
    }

    /** {@code e} and {@code p} of the form, as the fields of the input. */
    private static String written(String form) {
        return form.replaceAll("\\be\\b", "i.e.value").replaceAll("\\bp\\b", "i.p.value");
    }

    private static JsonNode behaviorNamed(JsonNode report, String name) {
        for (JsonNode each : report.get("modules").get(0).get("behaviors")) {
            if (each.get("name").asString().equals(name)) {
                return each;
            }
        }
        throw new AssertionError("no behavior " + name);
    }

    /** Whether the report says nothing of the behavior but that its numbers are read: no place is
     *  left not read for a reason that is not the rule relating the two. */
    private static boolean isRead(JsonNode behavior) {
        for (JsonNode each : behavior.get("partition").get("notRead")) {
            if (!each.get("reason").asString().equals("rule_relating_two_values")) {
                return false;
            }
        }
        return behavior.get("partition").get("axes").size() >= 2;
    }

    /** The classes of the axis of {@code place}, each as the whole numbers it holds. */
    private static List<int[]> classesOf(JsonNode behavior, String place) {
        List<int[]> out = new ArrayList<>();
        for (JsonNode axis : behavior.get("partition").get("axes")) {
            if (!axis.get("axis").asString().endsWith("/" + place)) {
                continue;
            }
            for (JsonNode label : axis.get("classes")) {
                Matcher matched = CLASS.matcher(label.asString());
                assertTrue(matched.matches(), "a class this reads: " + label);
                int least = Integer.parseInt(matched.group(1))
                        + (matched.group(2).equals("<") ? 1 : 0);
                int greatest = Integer.parseInt(matched.group(4))
                        - (matched.group(3).equals("<") ? 1 : 0);
                out.add(new int[] {least, greatest});
            }
        }
        assertTrue(!out.isEmpty(), "an axis of " + place);
        return out;
    }

    /**
     * What the program does at each pair: 0 where the way is not passed, 1 where it is and the
     * comparison comes out true, 2 where it comes out false, and -1 where the run stops.
     */
    private static int[][] outcomes(ClassLoader loader, int at) throws Exception {
        Object behavior = Emitted.behavior(loader, "demo", "b" + at)
                .getConstructor().newInstance();
        int[][] out = new int[TOP + 1][TOP + 1];
        for (int e = 0; e <= TOP; e++) {
            for (int p = 1; p <= TOP; p++) {
                Object in = Codecs.decoded(loader, "demo.In", Map.of("e", (long) e, "p", (long) p));
                try {
                    Object answer = Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
                    out[e][p] = switch (((Number) answer).intValue()) {
                        case 3 -> 0;
                        default -> ((Number) answer).intValue();
                    };
                } catch (ConstraintViolation stopped) {
                    out[e][p] = -1;
                }
            }
        }
        return out;
    }

    /**
     * Each value of {@code place}: whether the way is passed at some of the other number's values
     * and at all of them (bit 1 and bit 2), and how the comparison comes out at the rows that get
     * to it (bit 1 true, bit 2 false; none where no row gets there).
     */
    private static void heldToTheProgram(String form, String place, List<int[]> classes,
                                         int[][] outcomes) {
        boolean ofE = place.equals("i.e");
        int low = ofE ? 0 : 1;
        int[] way = new int[TOP + 1];
        int[] comparison = new int[TOP + 1];
        for (int value = low; value <= TOP; value++) {
            for (int other = ofE ? 1 : 0; other <= TOP; other++) {
                int outcome = ofE ? outcomes[value][other] : outcomes[other][value];
                assertTrue(outcome >= 0, form + ": a run stops at " + value + ", " + other);
                way[value] |= outcome == 0 ? 2 : 1;
                comparison[value] |= outcome == 1 ? 1 : outcome == 2 ? 2 : 0;
            }
        }
        // A class holds no two values the program tells apart: the way is passed alike at them,
        // and the comparison comes out alike at the rows that get to it where both have some.
        for (int[] each : classes) {
            for (int a = Math.max(each[0], low); a <= Math.min(each[1], TOP); a++) {
                for (int b = a + 1; b <= Math.min(each[1], TOP); b++) {
                    assertEquals(way[a], way[b], form + " " + place + ": " + a + " and " + b
                            + " are in one class, and the way is passed differently");
                    assertTrue(comparison[a] == 0 || comparison[b] == 0
                                    || comparison[a] == comparison[b],
                            form + " " + place + ": " + a + " and " + b + " are in one class, "
                                    + "and the comparison comes out differently");
                }
            }
        }
    }
}
