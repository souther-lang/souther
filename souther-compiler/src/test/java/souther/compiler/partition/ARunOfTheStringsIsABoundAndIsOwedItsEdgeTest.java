package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule whose strings are one stretch of the order they are measured on bounds the position, and
 * is owed the row at the place they begin.
 *
 * <p>{@code String.startsWith("JP", value)} admits exactly the strings from {@code "JP"} up to but
 * not including {@code "JQ"}, and a string is measured on the order the runtime compares them on. So
 * the position stops in two places, and a rule stating that in a comparison and one stating it as a
 * predicate leave it in the same two — the second was read as a rule holding the position to what it
 * admits and drawing no line, which is true of the format beside it and not of this.
 *
 * <p>What a rule states about the strings and where the strings stop are two questions here. The
 * first is settled by the reading that turns clauses into sets and is settled whether or not this
 * compiler could work out the text written in the rule; the second is asked only of a language it
 * has. So a format whose strings are not one stretch, and a rule this could read no language out of,
 * come back with no edge for reasons that are not the same reason.
 */
class ARunOfTheStringsIsABoundAndIsOwedItsEdgeTest {

    private static final String MODEL = """
            module runs

            data Pre    = String invariant String.startsWith("JP", value)
            data Cmp    = String invariant value >= "JP" && value < "JQ"
            data Same   = String invariant String.matches("JP[\\\\s\\\\S]*", value)
            data Format = String invariant String.matches("[0-9]{4}", value)
            data One    = String invariant String.matches("C", value)

            data Ok = { size: Int }

            behavior onPre : (v: Pre) -> Ok
                constructs Ok
            let onPre (v) = Ok { size = String.length(v.value) }

            behavior onCmp : (v: Cmp) -> Ok
                constructs Ok
            let onCmp (v) = Ok { size = String.length(v.value) }

            behavior onSame : (v: Same) -> Ok
                constructs Ok
            let onSame (v) = Ok { size = String.length(v.value) }

            behavior onFormat : (v: Format) -> Ok
                constructs Ok
            let onFormat (v) = Ok { size = String.length(v.value) }

            behavior onOne : (v: One) -> Ok
                constructs Ok
            let onOne (v) = Ok { size = String.length(v.value) }
            """;

    /**
     * The prefix and the comparison leave the position in the same places, and are owed the same
     * rows.
     *
     * <p>Compared as what the two are owed rather than as what a measure holds. A line is where a
     * row can be written against, and how many of those a measure keeps is this compiler's
     * arrangement; what has to agree is what an author is asked for.
     */
    @Test
    void aPrefixAndTheComparisonThatSaysItAreOwedTheSameRows() {
        String report = report(MODEL);

        assertEquals(owed(report, "onCmp"), owed(report, "onPre"),
                "the same strings leave the position in the same places:\n" + report);
    }

    /** And so is the pattern that accepts the same strings, whichever call states it. */
    @Test
    void andSoIsAPatternAcceptingTheSameStrings() {
        String report = report(MODEL);

        assertEquals(owed(report, "onCmp"), owed(report, "onSame"),
                "what a rule leaves is the strings it admits and not the call it is written as:\n"
                        + report);
    }

    /** The row is at the place the strings begin, and there is none at the place they stop: no
     *  string is at the second, and the order names none just below it. */
    @Test
    void theRowIsWhereTheStringsBeginAndNotWhereTheyStop() {
        String report = report(MODEL);

        assertTrue(report.contains(
                "undecided whether a row is at the ON point value = JP (invariant Pre #1)"), report);
        assertTrue(report.contains(
                "no ON point is owed at v = JQ (invariant Pre #1): this order names no value there"),
                report);
    }

    /**
     * A format whose strings are not one stretch holds the position to what it admits and draws no
     * line.
     *
     * <p>{@code [0-9]{4}} leaves out {@code "0000a"}, which is between two of the strings it
     * admits — so there are no two places to put an edge at, and what the rule does is what every
     * rule of this kind did before.
     */
    @Test
    void aFormatWhoseStringsAreNotOneStretchDrawsNoLine() {
        String report = report(MODEL);

        assertTrue(report.contains("no line: invariant Format #1 — it restricts this position to"
                + " the values it admits"), report);
        assertFalse(report.contains("(invariant Format #1):"),
                "and no edge is owed for it:\n" + report);
    }

    /**
     * And a rule admitting one string names a value rather than bounding a range.
     *
     * <p>One string is a stretch of the order like any other — it begins somewhere and ends at the
     * next string above it — and there is nothing between the two for a row to be owed at. What such
     * a rule leaves is what it admits, which is what a report says of it.
     */
    @Test
    void aRuleAdmittingOneStringNamesAValueRatherThanBoundingARange() {
        String report = report(MODEL);

        assertTrue(report.contains("no line: invariant One #1 — it restricts this position to"
                + " the values it admits"), report);
        assertFalse(report.contains("(invariant One #1):"), report);
    }

    /** What {@code behavior} is asked for, as the report writes it against the behavior's own
     *  positions. */
    private static String owed(String report, String behavior) {
        StringBuilder out = new StringBuilder();
        for (String line : report.lines().toList()) {
            if (line.contains("read as " + behavior + "/")) {
                out.append(line.substring(line.indexOf("read as ") + behavior.length() + 9))
                        .append('\n');
            }
        }
        return out.toString();
    }

    private static String report(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).human(SourceNameResolver.identity());
    }
}
