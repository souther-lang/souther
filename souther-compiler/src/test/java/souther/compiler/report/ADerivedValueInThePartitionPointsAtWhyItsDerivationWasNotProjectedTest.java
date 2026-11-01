package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule about a derived value is classified by the partition as one, and why the derivation was
 * not projected onto the input is the decision's own fact about the same comparison. The line of
 * the partition keeps its classification and points at that fact, at the comparison it was found
 * for and at no other.
 */
class ADerivedValueInThePartitionPointsAtWhyItsDerivationWasNotProjectedTest {

    private static final String MODEL = """
            module demo

            data Yes = { n: Int }
            data No = { n: Int }

            let late (c: Date, d: Date): Bool = Date.daysBetween(c, Date.addMonths(1, d)) >= 3

            behavior f : (c: Date, d: Date) -> Yes | No
            let f (c, d) = {
                if %s then Yes { n = 1 } else No { n = 0 }
            }
            """;

    private static final String DERIVED = "it is about a value made from this one";

    private static final String POINTER = "          · the decision, at the same comparison: not"
            + " composed against: a comparison over what Date.addMonths answers, a date moved by"
            + " months";

    private static List<String> report(String condition) {
        Compilation compilation = Compilation.ofSource(MODEL.formatted(condition), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), condition);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts())).lines().toList();
    }

    /** The line under each "not read" line that says {@code said}. */
    private static List<String> under(List<String> lines, String said) {
        List<String> out = new ArrayList<>();
        for (int at = 0; at < lines.size() - 1; at++) {
            if (lines.get(at).contains("not read: ") && lines.get(at).contains(said)) {
                out.add(lines.get(at + 1));
            }
        }
        return out;
    }

    /** The reason stays what the partition says, and the decision's is said under it. */
    @Test
    void aDerivedValueIsToldWhyItsDerivationWasNotProjected() {
        List<String> lines = report("Date.daysBetween(c, Date.addMonths(1, d)) >= 3");
        List<String> under = under(lines, DERIVED);
        assertEquals(2, under.size(), lines::toString);
        under.forEach(line -> assertTrue(line.startsWith(POINTER), line));
    }

    /** A helper's comparison is told the same at every call of it. */
    @Test
    void aDerivedValueInAHelperIsToldAtEveryCall() {
        List<String> lines = report("late(c, d) && late(d, c)");
        List<String> under = under(lines, DERIVED);
        assertEquals(2, under.size(), lines::toString);
        under.forEach(line -> assertTrue(line.startsWith(POINTER), line));
    }

    /** A derived value beside it is told its own reason and not the other's. */
    @Test
    void aDerivedValueBesideItIsNotToldTheReasonOfTheOther() {
        List<String> lines = report("late(c, d)"
                + " && Int.floorMod(Date.daysBetween(c, d), 7) + Date.daysBetween(c, d) >= 3");
        List<String> ofTheHelper = new ArrayList<>();
        List<String> ofTheOther = new ArrayList<>();
        for (int at = 0; at < lines.size() - 1; at++) {
            if (lines.get(at).contains("not read: ") && lines.get(at).contains(DERIVED)) {
                (lines.get(at).contains("late@") ? ofTheHelper : ofTheOther)
                        .add(lines.get(at + 1));
            }
        }
        assertEquals(2, ofTheHelper.size(), lines::toString);
        assertEquals(2, ofTheOther.size(), lines::toString);
        ofTheHelper.forEach(line -> assertTrue(line.startsWith(POINTER), line));
        ofTheOther.forEach(line -> assertTrue(line.contains("the decision, at the same"), line));
        ofTheOther.forEach(line -> assertFalse(line.contains("Date.addMonths"), line));
    }
}
