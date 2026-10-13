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

    /** What the rows holding nothing came to, measured once for both tests. */
    private static Map<Replacement, ReplacementEvidence.Outcome> holdingNothing;

    @Test
    void everyArmRewrittenAsItsSiblingIsShownByARowOnItsSideHoldingSomething() {
        Map<Replacement, ReplacementEvidence.Outcome> rewrites = measuredHoldingNothing();

        assertEquals(4, rewrites.size(), "each of the four arms as its sibling: " + rewrites);
        // The outer fork is the one written first, `elapsed < 0`; the inner one is `elapsed < 90`.
        int outer = rewrites.keySet().stream()
                .mapToInt(each -> ((Replacement.OfAnArm) each).fork().ordinal()).min()
                .orElseThrow();
        rewrites.forEach((rewrite, outcome) -> {
            Replacement.OfAnArm arm = (Replacement.OfAnArm) rewrite;
            List<String> inputs = shownBy(rewrite, outcome);
            assertFalse(inputs.get(2).contains("Megabytes(0)"),
                    "a row holding nothing answers alike down every arm: " + inputs);
            long elapsed = elapsed(row(inputs));
            boolean onItsSide = arm.fork().ordinal() == outer
                    ? (arm.part() == 0) == (elapsed < 0)
                    : elapsed >= 0 && (arm.part() == 0) == (elapsed < 90);
            assertTrue(onItsSide, "the row shown for " + rewrite + " goes down that arm, "
                    + elapsed + " days in: " + inputs);
        });
    }

    @Test
    void theRowsShowingThemTellEveryRewriteApartOnceAnswered() {
        Set<String> shown = new LinkedHashSet<>();
        measuredHoldingNothing().forEach((rewrite, outcome) ->
                shown.add(row(shownBy(rewrite, outcome))));
        List<String> rows = new ArrayList<>(HOLDING_NOTHING);
        rows.addAll(shown);

        Map<Replacement, ReplacementEvidence.Outcome> rewrites = armRewritesOf(modelWith(rows));

        assertEquals(4, rewrites.size(), "each of the four arms as its sibling: " + rewrites);
        assertTrue(rewrites.values().stream().allMatch(ReplacementEvidence.Noticed.class::isInstance),
                "every rewrite told apart by a row answered as the rule says: " + rewrites);
    }

    /**
     * An arm under a condition no reading of the way in states a row can be held to — an
     * {@code ||} of two inputs — is looked for from the rows seen going through it: the row shown
     * keeps what took the run there and moves what the arm answers with.
     */
    @Test
    void anArmNoReadingOfTheWayInStatesIsLookedForFromTheRowsSeenGoingThroughIt() {
        Map<Replacement, ReplacementEvidence.Outcome> rewrites = armRewritesOf("""
                module example.addon

                data Megabytes = Int

                behavior usable : (a: Bool, b: Bool, from: Date, on: Date, mb: Megabytes) -> Megabytes

                let usable (a, b, from, on, mb) =
                    if a || b then
                        if Date.daysBetween(from, on) < 90 then mb else Megabytes(0)
                    else Megabytes(0)

                example usable
                    | (true, false, Date("1970-01-01"), Date("1970-01-01"), Megabytes(0))
                        -> Megabytes(0)
                    | (true, false, Date("1969-10-03"), Date("1970-01-01"), Megabytes(0))
                        -> Megabytes(0)
                    | (false, false, Date("1970-01-01"), Date("1970-01-01"), Megabytes(0))
                        -> Megabytes(0)
                """);

        int outer = rewrites.keySet().stream()
                .mapToInt(each -> ((Replacement.OfAnArm) each).fork().ordinal()).min()
                .orElseThrow();
        Map.Entry<Replacement, ReplacementEvidence.Outcome> taken = rewrites.entrySet().stream()
                .filter(each -> each.getKey() instanceof Replacement.OfAnArm arm
                        && arm.fork().ordinal() == outer && arm.part() == 0)
                .findFirst().orElseThrow(() -> new AssertionError(
                        "the arm `a || b` takes, as its sibling: " + rewrites));
        List<String> inputs = shownBy(taken.getKey(), taken.getValue());
        assertTrue(inputs.get(0).equals("true") || inputs.get(1).equals("true"),
                "down the arm `a || b` takes: " + inputs);
        long elapsed = ChronoUnit.DAYS.between(LocalDate.parse(dateIn(inputs.get(2))),
                LocalDate.parse(dateIn(inputs.get(3))));
        assertTrue(elapsed >= 0 && elapsed < 90, "and inside the ninety days: " + inputs);
        assertFalse(inputs.get(4).contains("Megabytes(0)"),
                "holding something, which the arm answers and its sibling does not: " + inputs);
    }

    private static String dateIn(String written) {
        Matcher read = Pattern.compile("Date\\(\"([0-9-]+)\"\\)").matcher(written);
        assertTrue(read.matches(), "a date: " + written);
        return read.group(1);
    }

    private static synchronized Map<Replacement, ReplacementEvidence.Outcome>
            measuredHoldingNothing() {
        if (holdingNothing == null) {
            holdingNothing = armRewritesOf(modelWith(HOLDING_NOTHING));
        }
        return holdingNothing;
    }

    /** The inputs of the composed row {@code outcome} says shows {@code rewrite} differing. */
    private static List<String> shownBy(Replacement rewrite, ReplacementEvidence.Outcome outcome) {
        ReplacementEvidence.Unnoticed gap = assertInstanceOf(ReplacementEvidence.Unnoticed.class,
                outcome, "no written row tells " + rewrite + " apart, and a row shows it differs");
        return assertInstanceOf(ReplacementEvidence.ShownBy.AComposedRow.class, gap.shownBy(),
                "shown by a row composed for " + rewrite + ": " + gap.shownBy()).inputs();
    }

    private static String row(List<String> inputs) {
        return "(" + String.join(", ", inputs) + ")";
    }

    /** How many days from the row's purchase to the day it asks about. */
    private static long elapsed(String row) {
        Matcher read = read(row);
        return ChronoUnit.DAYS.between(LocalDate.parse(read.group(1)),
                LocalDate.parse(read.group(2)));
    }

    private static Matcher read(String row) {
        Matcher read = ROW.matcher(row);
        assertTrue(read.matches(), "a row of two dates and an amount: " + row);
        return read;
    }

    /** The rows, each answered as the add-on's rule says: the amount for ninety days counting
     *  the day of purchase, and nothing before or after. */
    private static String modelWith(List<String> rows) {
        StringBuilder out = new StringBuilder(BODY);
        for (String row : rows) {
            long elapsed = elapsed(row);
            String amount = elapsed >= 0 && elapsed < 90 ? read(row).group(3) : "0";
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
