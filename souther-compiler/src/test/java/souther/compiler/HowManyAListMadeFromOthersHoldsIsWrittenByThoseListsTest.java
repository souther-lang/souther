package souther.compiler;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many a list a body made of the input's lists holds is a number of those lists, so a rule
 * about it, added to another, is read and has rows written for it that hold as many as its points
 * ask.
 *
 * <p>Each model guards on a number of strings the two lists {@code ds} and {@code cs} come to, made
 * from them one way or another, and what is held is that the report reads the rule and that the
 * rows written hold, between the two lists, the numbers the points of the line ask for.
 */
class HowManyAListMadeFromOthersHoldsIsWrittenByThoseListsTest {

    private static String model(String guard) {
        return """
                module j1

                data Dup = { n: Int }
                data None1 = { z: Int }

                let one (e: String): List<String> = [e]

                behavior m : (ds: List<String>, cs: List<String>) -> Dup | None1
                let m (ds, cs) = {
                    guard %s else None1 { z = 0 }
                    Dup { n = 1 }
                }
                """.formatted(guard);
    }

    /**
     * Whether everything {@code report} says went unread is that a relation is not shown to reach
     * every value of a place: a sum of two sizes held against a number is one whose sizes each
     * settle it on their own past it, and no size of a list is declared to be had at every number.
     */
    private static boolean readSaveForWhatTheOtherValueReaches(String report) {
        return report.lines().filter(line -> line.strip().startsWith("· not read"))
                .allMatch(line -> line.contains("not shown to reach every value here"));
    }

    /** A list each element of which a closure answered one string for, beside another list. */
    @Test
    void whatAFlatMapAnsweredOneOfForEachElementIsReadBesideAnotherList() {
        for (String made : List.of("List.flatMap(e -> [ e ], ds)",
                "List.flatMap(e -> [ String.trim(e) ], ds)",
                "List.flatMap(e -> one(e), ds)",
                "{ let ma = List.flatMap(e -> [ e ], ds)\n ma }")) {
            Compilation compilation =
                    compiled(model("List.length(" + made + ") + List.length(cs) >= 1"));
            String report = report(compilation);
            assertTrue(readSaveForWhatTheOtherValueReaches(report), () -> made + ": " + report);
            assertFalse(report.contains("made from this one"), () -> made + ": " + report);
            List<Integer> held = heldByEachRow(rowsOf(compilation));
            assertTrue(held.contains(1), () -> made + ": the point on the line: " + held);
            assertTrue(held.contains(0), () -> made + ": the point just off it: " + held);
        }
    }

    /**
     * The model as it was reported: the list bound before the guard and answered in the result
     * too, so the size is read where the guard compares it and where the construction writes it.
     */
    @Test
    void theModelAsReportedIsReadAndHasItsRowsWritten() {
        Compilation compilation = compiled("""
                module j1

                data Dup = { n: Int }
                data None1 = { z: Int }

                behavior m : (ds: List<String>, cs: List<String>) -> Dup | None1
                let m (ds, cs) = {
                    let ma = List.flatMap(e -> [ e ], ds)
                    guard List.length(ma) + List.length(cs) >= 1 else None1 { z = 0 }
                    Dup { n = List.length(ma) }
                }
                """);
        String report = report(compilation);
        assertTrue(readSaveForWhatTheOtherValueReaches(report), report);
        assertFalse(report.contains("made from this one"), report);
        List<Integer> held = heldByEachRow(rowsOf(compilation));
        assertTrue(held.contains(1), () -> "the point on the line: " + held);
        assertTrue(held.contains(0), () -> "the point just off it: " + held);
    }

    /** As many as a mapping was handed, whether its closure answers the element or works
     *  something out of it. */
    @Test
    void whatAMappingHoldsIsWrittenAsTheListItMapped() {
        for (String closure : List.of("e -> e", "e -> String.trim(e)")) {
            Compilation compilation = compiled(model(
                    "List.length(List.map(" + closure + ", ds)) + List.length(cs) >= 2"));
            String report = report(compilation);
            assertTrue(readSaveForWhatTheOtherValueReaches(report),
                    () -> closure + ": " + report);
            List<Integer> held = heldByEachRow(rowsOf(compilation));
            assertTrue(held.contains(2), () -> closure + ": the point on the line: " + held);
            assertTrue(held.contains(1), () -> closure + ": the point just off it: " + held);
        }
    }

    /** How many strings each row writes, over both lists. */
    private static List<Integer> heldByEachRow(String rows) {
        List<Integer> held = new ArrayList<>();
        for (String line : rows.split("\n")) {
            if (line.trim().startsWith("| (")) {
                held.add(count(line.substring(0, line.indexOf("->")), "\"[^\"]*\""));
            }
        }
        return held;
    }

    private static int count(String text, String regex) {
        Matcher found = Pattern.compile(regex).matcher(text);
        int n = 0;
        while (found.find()) {
            n++;
        }
        return n;
    }

    private static String rowsOf(Compilation compilation) {
        return GeneratedRows.of(compilation, null, null,
                SourceRendering.namedByIdentity(SourceLayouts.NONE)).text();
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static Compilation compiled(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(),
                () -> "the source compiles: " + model);
        return compilation;
    }
}
