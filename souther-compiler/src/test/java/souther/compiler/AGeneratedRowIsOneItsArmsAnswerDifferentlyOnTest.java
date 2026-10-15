package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Offering;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.time.LocalDate;
import java.time.temporal.ChronoUnit;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row composed for what a search was asked — a point of a line, a class — is one the rewrites of
 * the arms it goes through answer differently on, where one is among the rows that meet it.
 *
 * <p>The model the question came from. The amount is read by no rule, so every row at a point of
 * the dates stands there whatever it holds; composed from its first value, every row answered
 * nothing, and the arm answering the amount could not be told from the arms answering nothing until
 * a second round composed more rows.
 */
class AGeneratedRowIsOneItsArmsAnswerDifferentlyOnTest {

    /** A fork on the cases of a sum, one arm answering what the row holds and one answering 0. */
    private static final String BONUS = """
            module example.bonus

            data Gold
            data Plain
            data Kind = Gold | Plain
            data Points = Int

            behavior bonus : (kind: Kind, earned: Points) -> Points

            let bonus (kind, earned) = match kind with
                | Gold -> earned
                | Plain -> Points(0)
            """;

    /** A row of that block, as it is offered. */
    private static final Pattern CASE_ROW = Pattern.compile(
            "\\(([A-Za-z]+), Points\\((-?[0-9]+)\\)\\)\\s*-> <\\?>");

    /**
     * The rows composed for the cases of the sum, answered, tell each arm from the other: the row
     * for the case answering what it holds holds something to answer.
     */
    @Test
    void theRowsForEachCaseAnsweredTellTheArmsApart() {
        String block = blockOf(BONUS, "example.bonus");
        StringBuilder rows = new StringBuilder();
        for (String line : block.lines().filter(line -> !line.startsWith("//")).toList()) {
            Matcher row = CASE_ROW.matcher(line);
            rows.append(!row.find() ? line : line.replace("<?>", "Points("
                    + (row.group(1).equals("Gold") ? row.group(2) : "0") + ")")).append('\n');
        }
        Compilation compilation = compiled(BONUS + "\n" + rows);
        String page = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));

        assertTrue(page.contains("replacement 2/2"), () -> rows + "\n" + page);
        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED,
                AdequacyReport.of(compilation).adequacy(), () -> rows + "\n" + page);
    }

    private static final String ADDON = """
            module example.addon

            data Megabytes = Int

            behavior usable : (purchased: Date, on: Date, amount: Megabytes) -> Megabytes

            // An add-on is usable for 90 days, counting the day of purchase as the first.
            let usable (purchased, on, amount) = {
                let elapsed = Date.daysBetween(purchased, on)
                if elapsed < 0 then Megabytes(0)
                else if elapsed < 90 then amount
                else Megabytes(0)
            }
            """;

    /** One row of the block, as it is offered. */
    private static final Pattern ROW = Pattern.compile(
            "\\| \\(Date\\(\"([0-9-]+)\"\\), Date\\(\"([0-9-]+)\"\\), Megabytes\\((-?[0-9]+)\\)\\)"
                    + " -> <\\?>");

    /**
     * The first round's rows, answered, are every row the behavior is owed: a strict build has no
     * gap to refuse over with nothing else written, and nothing more is offered.
     *
     * <p>Not satisfied outright: one comparison relates the two dates in a way this compiler does
     * not read, and that keeps the verdict open whatever the rows are.
     */
    @Test
    void theFirstRoundsRowsAnsweredSettleTheRewritesOfEveryArm() {
        String block = blockOf(ADDON, "example.addon");
        String rows = answered(block);
        String source = ADDON + "\n" + rows;

        Compilation compilation = compiled(source);
        String page = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertNotEquals(AdequacyReport.AdequacyStatus.NOT_SATISFIED,
                AdequacyReport.of(compilation).adequacy(), () -> rows + "\n" + page);
        assertTrue(page.contains("replacement 4/4"), () -> "every rewrite told apart: " + page);
        assertTrue(page.contains("obligations 8/8"), () -> "every point stood at: " + page);
        assertEquals("", blockOf(source, "example.addon"), "and nothing is offered again");
    }

    /**
     * Arms the rules leave answering alike on every row are still arms a row is owed at each point
     * of the line over them: nothing telling them apart is a preference that found nothing, and not
     * a point no row stands at.
     */
    @Test
    void armsNoRowTellsApartStillHaveARowAtEveryPoint() {
        String alike = """
                module example.alike

                data Score = Int
                    invariant nothing = value == 0

                behavior classify : (x: Int, bonus: Score) -> Score

                let classify (x, bonus) = if x < 10 then bonus else Score(0)
                """;

        List<String> xs = rowsIn(blockOf(alike, "example.alike")).stream()
                .map(row -> row.substring(row.indexOf('(') + 1, row.indexOf(',')))
                .sorted().toList();
        assertEquals(List.of("10", "11", "8", "9"), xs,
                "a row at the line's ON, OFF, IN and OUT points");
    }

    /** The answer the behavior gives a row, worked out here from what the comment above it says. */
    private static String answered(String block) {
        StringBuilder out = new StringBuilder();
        for (String line : block.lines().filter(line -> !line.startsWith("//")).toList()) {
            Matcher row = ROW.matcher(line);
            if (!row.find()) {
                out.append(line).append('\n');
                continue;
            }
            long elapsed = ChronoUnit.DAYS.between(LocalDate.parse(row.group(1)),
                    LocalDate.parse(row.group(2)));
            String amount = elapsed >= 0 && elapsed < 90 ? row.group(3) : "0";
            out.append(line.replace("<?>", "Megabytes(" + amount + ")")).append('\n');
        }
        return out.toString();
    }

    private static List<String> rowsIn(String block) {
        return block.lines().filter(line -> line.trim().startsWith("|")).toList();
    }

    private static String blockOf(String source, String module) {
        Compilation compilation = compiled(source);
        Offering offering = Adequacy.offeredFor(compilation.db(),
                OfferingRequest.overTheModule(module));
        assertNotNull(offering, "the model under test compiles");
        return GeneratedRows.of(offering, Map.of(),
                SourceRendering.namedByIdentity(compilation.texts()), compilation.db()).text();
    }

    private static Compilation compiled(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return compilation;
    }
}
