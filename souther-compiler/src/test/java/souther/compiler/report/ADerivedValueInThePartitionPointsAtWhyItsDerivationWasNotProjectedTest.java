package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line of the partition that stops at a comparison is told what the decision's searches went
 * without at the same comparison, rule by rule. The classification is the partition's and stays;
 * what is added is a pointer, and a pointer is held to what it points at: it names a search the
 * decision section shows, says what that section says of it, and follows its order.
 */
class ADerivedValueInThePartitionPointsAtWhyItsDerivationWasNotProjectedTest {

    private static final String MODEL = """
            module demo

            data Yes = { n: Int }
            data No = { n: Int }
            data Maybe = { n: Int }

            let late (c: Date, d: Date): Bool = Date.daysBetween(c, Date.addMonths(1, d)) >= 3

            behavior f : (c: Date, d: Date) -> Yes | No | Maybe
            let f (c, d) = {
                %s
            }
            """;

    private static final String DERIVED = "it is about a value made from this one";

    private static final Pattern POINTER = Pattern.compile(
            "^ {10}· the decision, at the rule where (.+): not composed against: (.+)$");

    private static final Pattern BULLET = Pattern.compile("^ {10}· (.+)$");

    /** What a search of the decision section is told as: the rule, and what it went without. */
    private record Search(String rule, String left) { }

    private static List<String> report(String body) {
        Compilation compilation = Compilation.ofSource(MODEL.formatted(body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), body);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts())).lines().toList();
    }

    /** Each search the decision section shows with something left out, in the order it shows. */
    private static List<Search> shown(List<String> lines) {
        List<Search> out = new ArrayList<>();
        List<String> rule = null;
        for (String line : lines) {
            if (line.matches("^ {6}\\S.*")) {
                rule = line.startsWith("      ? nothing could show") ? new ArrayList<>() : null;
                continue;
            }
            Matcher bullet = BULLET.matcher(line);
            if (rule != null && bullet.matches()) {
                String text = bullet.group(1);
                if (text.startsWith("not composed against: ")) {
                    out.add(new Search(String.join(" and ", rule),
                            text.substring("not composed against: ".length())));
                } else {
                    rule.add(text);
                }
            }
        }
        return out;
    }

    /** The pointers under each "not read" line that says {@code said}, one list per line. */
    private static List<List<Search>> pointedAt(List<String> lines, String said) {
        List<List<Search>> out = new ArrayList<>();
        for (int at = 0; at < lines.size(); at++) {
            if (!lines.get(at).contains("not read: ") || !lines.get(at).contains(said)) {
                continue;
            }
            List<Search> under = new ArrayList<>();
            for (int next = at + 1; next < lines.size(); next++) {
                Matcher pointer = POINTER.matcher(lines.get(next));
                if (!pointer.matches()) {
                    break;
                }
                under.add(new Search(pointer.group(1), pointer.group(2)));
            }
            out.add(under);
        }
        return out;
    }

    /** Every pointer of {@code lines} is a search the decision section shows, said as it says it,
     *  and in the order it shows them. */
    private static void everyPointerIsAnswered(List<String> lines) {
        List<Search> shown = shown(lines);
        for (List<Search> under : pointedAt(lines, "")) {
            int after = -1;
            for (Search pointer : under) {
                int at = shown.indexOf(pointer);
                assertTrue(at >= 0, pointer + " is not shown by the decision section: " + shown);
                assertTrue(at > after, "out of the order the decision section shows: " + under);
                after = at;
            }
        }
    }

    /** The issue's comparison: told which rule, in the words of the decision section. */
    @Test
    void aDerivedValueIsToldWhichSearchWentWithoutItsDerivation() {
        List<String> lines = report("if late(c, d) then Yes { n = 1 } else No { n = 0 }");
        List<List<Search>> pointed = pointedAt(lines, DERIVED);
        assertEquals(2, pointed.size(), lines::toString);
        for (List<Search> under : pointed) {
            assertEquals(1, under.size(), lines::toString);
            assertTrue(under.getFirst().rule().contains("does not hold"), under::toString);
            assertTrue(under.getFirst().left().contains("a date moved by months"),
                    under::toString);
        }
        everyPointerIsAnswered(lines);
    }

    /** Two searches through one comparison are told apart by their rule, in the order the decision
     *  section shows them, and none is dropped for saying what another says. */
    @Test
    void everySearchThroughTheComparisonIsToldByItsRuleInTheOrderShown() {
        List<String> lines = report("if late(c, d) then (if late(c, c) then Yes { n = 1 }"
                + " else No { n = 0 }) else Maybe { n = 2 }");
        List<Search> shown = shown(lines);
        assertEquals(2, shown.size(), lines::toString);
        for (List<Search> under : pointedAt(lines, DERIVED)) {
            assertEquals(shown, under, lines::toString);
        }
        everyPointerIsAnswered(lines);
    }

    /** A search the decision section does not show is not pointed at, though the rule's own
     *  reading stopped: it settled the rule, and a pointer to it would point at nothing. */
    @Test
    void aSearchTheDecisionSectionDoesNotShowIsNotPointedAt() {
        List<String> lines = report("if late(c, d) && Date.daysBetween(c, d) >= 5"
                + " then Yes { n = 1 } else No { n = 0 }");
        assertEquals(List.of(), shown(lines), lines::toString);
        assertFalse(pointedAt(lines, DERIVED).isEmpty(), lines::toString);
        pointedAt(lines, "").forEach(under -> assertEquals(List.of(), under, lines::toString));
    }

    /** A derived value beside it is told its own reason and not the other's. */
    @Test
    void aDerivedValueBesideItIsNotToldTheReasonOfTheOther() {
        List<String> lines = report("if late(c, d) && Int.floorMod(Date.daysBetween(c, d), 7)"
                + " + Date.daysBetween(c, d) >= 3 then Yes { n = 1 } else No { n = 0 }");
        List<Boolean> ofTheHelper = new ArrayList<>();
        for (int at = 0; at < lines.size(); at++) {
            if (lines.get(at).contains("not read: ") && lines.get(at).contains(DERIVED)) {
                boolean helper = lines.get(at).contains("late@");
                for (List<Search> under : pointedAt(List.of(lines.get(at), lines.get(at + 1)),
                        DERIVED)) {
                    for (Search each : under) {
                        assertEquals(helper, each.left().contains("Date.addMonths"), each::toString);
                    }
                }
                ofTheHelper.add(helper);
            }
        }
        assertTrue(ofTheHelper.contains(true) && ofTheHelper.contains(false), lines::toString);
        everyPointerIsAnswered(lines);
    }
}
