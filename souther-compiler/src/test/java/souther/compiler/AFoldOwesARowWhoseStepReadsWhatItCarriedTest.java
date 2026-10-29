package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Located;
import souther.compiler.diag.Messages;
import souther.compiler.diag.Primary;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.List;
import java.util.Locale;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A fold owes a row in which its step reads what an earlier step answered, and a row of fewer than
 * two elements is not one.
 *
 * <p>A row of no element runs no step, and a row of one element runs the step once, on the seed. A
 * sum whose rows are those cannot be told from the fold stopping after its first element, nor from
 * every step being handed the seed in the place of what it carries: the seed is {@code 0}, which is
 * what {@code +} leaves alone. Both rewrites are asked of every fold a row enters, and a row of two
 * elements tells both apart.
 */
class AFoldOwesARowWhoseStepReadsWhatItCarriedTest {

    private static String total(String step, String rows) {
        return """
                module repro.total

                behavior total : (xs: List<Int>) -> Int

                let total (xs) = List.fold(%s, 0, xs)

                example total
                    | "nothing" : ([]) -> 0
                    | "one" : ([1]) -> 1
                %s""".formatted(step, rows);
    }

    private static final String SUM = total("(acc, x) -> acc + x", "");

    private static final String STOPS_AFTER_ONE_STEP =
            "! no row would come out differently if the fold (5:18) stopped after its first element";

    private static final String STEPS_FROM_THE_SEED =
            "! no row would come out differently if the fold (5:18) handed each step the seed in"
                    + " place of what the step before it answered";

    @Test
    void rowsOfFewerThanTwoElementsLeaveBothRewritesOfTheFoldAGap() {
        Compilation compilation = measured(SUM);

        assertEquals(List.of(STOPS_AFTER_ONE_STEP, STEPS_FROM_THE_SEED), rewriteLines(compilation));
        assertEquals(AdequacyReport.AdequacyStatus.NOT_SATISFIED,
                AdequacyReport.of(compilation).adequacy());
    }

    @Test
    void aRowOfTwoElementsTellsBothApart() {
        Compilation compilation =
                measured(total("(acc, x) -> acc + x", "    | \"two\" : ([3, 4]) -> 7\n"));

        assertEquals(List.of(), rewriteLines(compilation));
        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED,
                AdequacyReport.of(compilation).adequacy());
    }

    /**
     * A step that never reads what it carries is the fold under another spelling once it is handed
     * the seed, and is not asked about that; stopping after one step is still another program, and
     * the two rows still cannot tell a fold keeping the last element from one keeping the first.
     */
    @Test
    void aStepThatNeverReadsWhatItCarriesIsAskedOnlyWhetherTheFoldGoesOn() {
        Compilation compilation = measured(total("(acc, x) -> x", ""));

        assertEquals(List.of(STOPS_AFTER_ONE_STEP), rewriteLines(compilation));
        // Not asked, rather than left open: the two values the rows came to and the one rewrite.
        assertTrue(page(compilation).lines().map(String::strip)
                        .anyMatch("replacement 2/3"::equals),
                () -> page(compilation));
    }

    /** A list written with one element is walked no further than its first, by either rewrite. */
    @Test
    void aListWrittenWithOneElementIsAWalkNeitherRewriteChanges() {
        Compilation compilation = measured("""
                module repro.one

                behavior plus : (n: Int) -> Int

                let plus (n) = List.fold((acc, x) -> acc + x, 0, [n])

                example plus
                    | "zero" : (0) -> 0
                    | "one" : (1) -> 1
                """);

        // The two values the rows came to, and nothing of the fold: not asked, rather than left
        // open for want of an input the search could not find.
        assertTrue(page(compilation).lines().map(String::strip)
                        .anyMatch("replacement 2/2"::equals),
                () -> page(compilation));
    }

    /** The row offered holds two elements, and is one row for both rewrites. */
    @Test
    void theRowOfferedHoldsTwoElementsAndIsOneRowForBoth() {
        Compilation compilation = measured(SUM);
        String block = GeneratedRows.of(Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("repro.total")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();

        List<RowsOfABlock.Row> rows = RowsOfABlock.of(block);
        assertEquals(1, rows.size(), () -> "one row: " + block);
        RowsOfABlock.Row row = rows.getFirst();
        assertTrue(row.isFor("the fold stopping after its first element")
                        && row.isFor("each step of the fold handed the seed"),
                () -> "for both rewrites: " + block);
        assertTrue(row.values().matches("\\(\\[-?\\d+, -?\\d+]\\) -> <\\?>"),
                () -> "a list of two elements: " + block);
    }

    /** A build is warned at the fold, and told which row to write. */
    @Test
    void aBuildIsWarnedAtTheFold() {
        Compilation compilation = warned(SUM);
        List<Located> warnings = rewriteWarnings(compilation);

        assertEquals(List.of(
                        "No row of `total` would come out differently if this fold stopped after"
                                + " its first element.",
                        "No row of `total` would come out differently if each step of this fold"
                                + " were handed the seed in place of what the step before it"
                                + " answered."),
                warnings.stream()
                        .map(each -> Messages.render(each.diagnostic().said(), Locale.ENGLISH))
                        .toList());
        for (Located each : warnings) {
            Primary.InSource at =
                    assertInstanceOf(Primary.InSource.class, each.diagnostic().primary());
            assertEquals(5, WhereItSits.in(SUM, at.place().region()).start().line(),
                    "the line of the fold");
            assertTrue(each.diagnostic().notes().stream()
                            .map(n -> Messages.render(n.said(), Locale.ENGLISH))
                            .anyMatch(n -> n.startsWith("Write a row at ([")),
                    () -> "and the row to write: " + each.diagnostic().notes());
        }
    }

    /**
     * A fold inside one of the language's own operations is one no row of fewer than two elements
     * tells apart either, and is said by the definition that wrote it, at the behavior: this build
     * holds no source of it to point at.
     */
    @Test
    void aFoldTheLanguageWritesIsSaidByTheDefinitionThatWroteIt() {
        Compilation compilation = warned("""
                module repro.mapped

                behavior doubled : (xs: List<Int>) -> List<Int>

                let doubled (xs) = List.map(x -> x * 2, xs)

                example doubled
                    | "nothing" : ([]) -> []
                    | "one" : ([1]) -> [2]
                """);

        assertEquals(List.of(
                        "No row of `doubled` would come out differently if a fold of"
                                + " `souther.list.map`, which this build holds no source of,"
                                + " stopped after its first element.",
                        "No row of `doubled` would come out differently if each step of a fold of"
                                + " `souther.list.map`, which this build holds no source of, were"
                                + " handed the seed in place of what the step before it answered."),
                rewriteWarnings(compilation).stream()
                        .map(each -> Messages.render(each.diagnostic().said(), Locale.ENGLISH))
                        .toList());
    }

    private static String page(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static List<String> rewriteLines(Compilation compilation) {
        return page(compilation).lines().map(String::strip)
                .filter(line -> line.startsWith("! no row would come out differently"))
                .toList();
    }

    private static List<Located> rewriteWarnings(Compilation compilation) {
        return compilation.warnings().stream()
                .filter(each -> "E1939".equals(each.diagnostic().code().toString()))
                .toList();
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return compilation;
    }

    private static Compilation warned(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        compilation.answerEverything();
        return compilation;
    }
}
