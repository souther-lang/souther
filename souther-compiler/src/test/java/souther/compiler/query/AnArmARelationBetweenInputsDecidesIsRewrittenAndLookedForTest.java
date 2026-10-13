package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.partition.Replacement;

import java.time.LocalDate;
import java.time.temporal.ChronoUnit;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rewrite of an arm a comparison between two inputs decides is looked for where the comparison
 * comes out the arm's way, and the row found there is one writing its answer down tells the
 * rewrite apart with.
 *
 * <p>The comparison is of how many days lie between two dates, so no class of either date stands
 * for a side of it. The rows hold the amount at nothing, which every arm answers alike; a row that
 * would notice an arm answering as its sibling has to hold something else there, and has to be on
 * the arm's side of the comparison as well.
 */
class AnArmARelationBetweenInputsDecidesIsRewrittenAndLookedForTest {

    private static final String BODY = """
            module example.addon

            data Megabytes = Int

            behavior usable : (purchased: Date, on: Date, amount: Megabytes) -> Megabytes

            let usable (purchased, on, amount) = {
                let elapsed = Date.daysBetween(purchased, on)
                if elapsed < 0 then Megabytes(0)
                else if elapsed < 90 then amount
                else Megabytes(0)
            }

            example usable
            """;

    /** One row either side of each end of the ninety days, every one holding nothing. */
    private static final List<String> HOLDING_NOTHING = List.of(
            "(Date(\"1970-01-02\"), Date(\"1970-01-01\"), Megabytes(0))",
            "(Date(\"1970-01-01\"), Date(\"1970-01-01\"), Megabytes(0))",
            "(Date(\"1970-01-03\"), Date(\"1970-01-01\"), Megabytes(0))",
            "(Date(\"1969-10-04\"), Date(\"1970-01-01\"), Megabytes(0))",
            "(Date(\"1969-10-03\"), Date(\"1970-01-01\"), Megabytes(0))",
            "(Date(\"1969-10-02\"), Date(\"1970-01-01\"), Megabytes(0))");

    private static final Pattern ROW = Pattern.compile(
            "\\(Date\\(\"([0-9-]+)\"\\), Date\\(\"([0-9-]+)\"\\), Megabytes\\((-?[0-9]+)\\)\\)");

    @Test
    void everyArmRewrittenAsItsSiblingIsShownByARowHoldingSomething() {
        Map<Replacement, ReplacementEvidence.Outcome> rewrites =
                armRewritesOf(modelWith(HOLDING_NOTHING));

        assertEquals(4, rewrites.size(), "each of the four arms as its sibling: " + rewrites);
        rewrites.forEach((rewrite, outcome) -> {
            ReplacementEvidence.Unnoticed gap = assertInstanceOf(
                    ReplacementEvidence.Unnoticed.class, outcome,
                    "no written row tells " + rewrite + " apart, and a row shows it differs");
            ReplacementEvidence.ShownBy.AComposedRow shown = assertInstanceOf(
                    ReplacementEvidence.ShownBy.AComposedRow.class, gap.shownBy(),
                    "shown by a row composed for it: " + gap.shownBy());
            assertFalse(shown.inputs().get(2).contains("Megabytes(0)"),
                    "a row holding nothing answers alike down every arm: " + shown.inputs());
        });
    }

    @Test
    void theRowsShowingThemTellEveryRewriteApartOnceAnswered() {
        Set<String> shown = new LinkedHashSet<>();
        armRewritesOf(modelWith(HOLDING_NOTHING)).values().forEach(outcome -> shown.add(
                "(" + String.join(", ", ((ReplacementEvidence.ShownBy.AComposedRow)
                        ((ReplacementEvidence.Unnoticed) outcome).shownBy()).inputs()) + ")"));
        List<String> rows = new ArrayList<>(HOLDING_NOTHING);
        rows.addAll(shown);

        Map<Replacement, ReplacementEvidence.Outcome> rewrites = armRewritesOf(modelWith(rows));

        assertEquals(4, rewrites.size(), "each of the four arms as its sibling: " + rewrites);
        assertTrue(rewrites.values().stream().allMatch(ReplacementEvidence.Noticed.class::isInstance),
                "every rewrite told apart by a row answered as the rule says: " + rewrites);
    }

    /** The rows, each answered as the add-on's rule says: the amount for ninety days counting
     *  the day of purchase, and nothing before or after. */
    private static String modelWith(List<String> rows) {
        StringBuilder out = new StringBuilder(BODY);
        for (String row : rows) {
            Matcher read = ROW.matcher(row);
            assertTrue(read.matches(), "a row of two dates and an amount: " + row);
            long elapsed = ChronoUnit.DAYS.between(LocalDate.parse(read.group(1)),
                    LocalDate.parse(read.group(2)));
            String amount = elapsed >= 0 && elapsed < 90 ? read.group(3) : "0";
            out.append("    | ").append(row).append(" -> Megabytes(").append(amount)
                    .append(")\n");
        }
        return out.toString();
    }

    private static Map<Replacement, ReplacementEvidence.Outcome> armRewritesOf(String source) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code()).toList(),
                "the model under test compiles");
        ReplacementEvidence its = compilation.db()
                .ask(new Replacements.Measured(compilation.modules().get(0))).value()
                .get("usable");
        Map<Replacement, ReplacementEvidence.Outcome> out = new LinkedHashMap<>();
        its.measured().made().orElseThrow(() -> new AssertionError(
                        "the rewrites were measured: " + its.measured()))
                .rewrites().forEach(each -> {
                    if (each.replacement() instanceof Replacement.OfAnArm) {
                        out.put(each.replacement(), each.outcome());
                    }
                });
        return out;
    }
}
