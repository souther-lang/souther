package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A module whose declarations were read short, and found no line, no debt and no exclusion, says
 * what they went without under a heading of their own.
 *
 * <p>Not under the last behavior, which is where a line at a behavior's indent reads as belonging,
 * and not as a count: nothing found is not nothing is owed, so a heading that said {@code 0/0} would
 * claim a reading that was not made.
 */
class ADeclarationsReadShortThatFoundNothingSayWhatTheyWentWithoutUnderTheirOwnHeadingTest {

    /** A rule about a number this reading cannot name: the declarations cannot place its line. */
    private static final String SOURCE = """
            module demo

            data Yes
            data No
            data Answer = Yes | No

            data N = { n: Int, s: String }
                invariant r = n >= 2 || Int.abs(n) >= 5

            behavior check : (v: N) -> Answer
            let check (v) = Yes
            """;

    private static List<String> page() {
        Compilation compilation = ACompiledModel.measured(SOURCE, Adequacy.Asked.fullReport());
        return AdequacyReport.of(compilation).humanInEnglish(
                SourceRendering.namedByIdentity(compilation.texts())).lines().toList();
    }

    @Test
    void theHeadingIsThereAndClaimsNoCount() {
        List<String> lines = page();

        assertTrue(lines.contains("  declarations"), String.join("\n", lines));
    }

    @Test
    void whatTheyWentWithoutIsSaidUnderTheHeadingAndNotUnderTheBehavior() {
        List<String> lines = page();
        int heading = lines.indexOf("  declarations");

        assertTrue(heading >= 0, String.join("\n", lines));
        assertTrue(lines.get(heading + 1).startsWith("      ? partial: "),
                "under the heading, one level in from it: " + lines.get(heading + 1));
        // And none at a behavior's indent after it, which is where a line of the declarations
        // reads as the last behavior's.
        long after = lines.subList(heading + 1, lines.size()).stream()
                .filter(line -> line.startsWith("    ? partial: ")).count();
        assertEquals(0, after, "nothing after the heading is said at a behavior's indent");
        assertFalse(lines.get(heading).contains("/"), "no count is claimed: " + lines.get(heading));
    }
}
