package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A point whose row was composed without part of the way says that first, and the word the search
 * came back with follows it.
 *
 * <p>The word is about what was tried; what the way left out is about what it was tried with.
 * Opened on the word alone, a reader is told a search had everything and reached nothing, and goes
 * looking for a row nothing can write — where what happened is that no search of the whole thing
 * was ever made.
 *
 * <p><b>Whichever stage let the condition go.</b> A condition the walk had no words for, one it
 * stated that nothing could place a position of, and one it stated that meets a location the row
 * is already being written for are three different things to do something about, and the row was
 * composed without all three of them alike. Written for one of them, this would be a sentence
 * about the case somebody happened to be looking at.
 *
 * <p><b>Coverage and not cause.</b> Nothing here composed against those conditions, so what a
 * search with them in would have found is not something to say. The sentence that keeps the point
 * open stays where it was.
 */
class WhatTheWayLeftOutIsSaidBeforeWhatTheSearchCameToTest {

    /** A condition above the line measuring a location the comparison below it compares. */
    private static final String A_MEASURE_OF_A_COMPARED_POSITION = """
            module example.shared

            data Yes = { v: Int }
            data No = { why: Int }

            behavior cmp : (a: String, b: String) -> Yes | No
                constructs Yes
                constructs No

            let cmp (a, b) = {
                guard String.length(b) /= 1 else No { why = 0 }
                guard a < b else No { why = 1 }
                Yes { v = 1 }
            }
            """;

    /** The same, where both demands are numbers taken of one location on one carrier. */
    private static final String TWO_MEASURES_OF_ONE_LOCATION = """
            module example.shared

            data Yes = { v: Int }
            data No = { why: Int }

            behavior at : (t: Time) -> Yes | No
                constructs Yes
                constructs No

            let at (t) = {
                guard Time.hour(t) /= 0 else No { why = 0 }
                guard Time.minute(t) < 30 else No { why = 1 }
                Yes { v = 1 }
            }
            """;

    /** A condition above the line over positions nothing composed a value at. */
    private static final String POSITIONS_NOTHING_COMPOSED_A_VALUE_AT = """
            module example.positions

            data Yes = { v: Int }
            data No = { why: Int }

            behavior f : (a: String, b: String, n: Int) -> Yes | No
                constructs Yes
                constructs No

            let f (a, b, n) = {
                guard a < b else No { why = 0 }
                guard n < 10 else No { why = 1 }
                Yes { v = 1 }
            }
            """;

    /** And one the walk had no words for at all, which never reached the composer. */
    private static final String A_SHAPE_THE_WALK_HAS_NO_WORDS_FOR = """
            module example.unstated

            data Yes = { v: Int }
            data No = { why: Int }

            behavior f : (s: String, n: Int) -> Yes | No
                constructs Yes
                constructs No

            let f (s, n) = {
                guard String.matches("(a+)\\\\1", s) else No { why = 0 }
                guard n < 10 else No { why = 1 }
                Yes { v = 1 }
            }
            """;

    /**
     * A point nothing composed a row for with the way used whole, which is the control.
     *
     * <p>Its search was over everything the point asks, so the clause this puts first would be one
     * written for a search that left nothing out. This is the shape of #1654 and not of this one,
     * which is the second thing it holds: the two are not one sentence.
     */
    private static final String THE_WAY_WAS_USED_WHOLE = """
            module example.apart

            data Yes = { v: Int }
            data No = { why: Int }

            behavior f : (xs: List<Int>, n: Int) -> Yes | No
                constructs Yes
                constructs No

            let f (xs, n) = {
                guard List.length(xs) < n else No { why = 1 }
                Yes { v = 1 }
            }
            """;

    private static final String LEFT_OUT =
            "not every condition on the way to the line is one the row was composed against";

    /**
     * Every stage the walk classifies, because what is being held is the shape and not the case
     * this was found through.
     */
    @Test
    void whateverLetTheConditionGoIsSaidBeforeTheSearchesWord() {
        for (String model : List.of(A_MEASURE_OF_A_COMPARED_POSITION, TWO_MEASURES_OF_ONE_LOCATION,
                POSITIONS_NOTHING_COMPOSED_A_VALUE_AT, A_SHAPE_THE_WALK_HAS_NO_WORDS_FOR)) {
            List<String> said = whereNothingCouldShowARow(model);

            assertFalse(said.isEmpty(), () -> "this model has points nothing composed a row for:\n"
                    + model);
            for (String each : said) {
                assertTrue(each.contains("— " + LEFT_OUT + ":"),
                        () -> "the line opens on what the way left out: " + each);
                assertTrue(each.indexOf(LEFT_OUT) < each.indexOf("nothing composed one:"),
                        () -> "and the search's own word follows it: " + each);
            }
        }
    }

    /**
     * And the stages keep their own words, so a reader is still told which of them it was.
     *
     * <p>Three models and three sentences. Put first without this, the clause could have been one
     * wording for every way a condition goes unrepresented, which is the distinction the stages
     * exist to carry.
     */
    @Test
    void whichStageLetItGoIsStillSaid() {
        assertTrue(only(A_MEASURE_OF_A_COMPARED_POSITION).contains("a condition on another number"
                        + " taken where this row is already being written for one"),
                () -> only(A_MEASURE_OF_A_COMPARED_POSITION));
        assertTrue(only(POSITIONS_NOTHING_COMPOSED_A_VALUE_AT).contains(
                        "a condition on positions nothing here composed a value at"),
                () -> only(POSITIONS_NOTHING_COMPOSED_A_VALUE_AT));
        assertTrue(only(A_SHAPE_THE_WALK_HAS_NO_WORDS_FOR).contains(
                        "a condition that is neither a comparison nor a combination of them"),
                () -> only(A_SHAPE_THE_WALK_HAS_NO_WORDS_FOR));
    }

    /**
     * And nothing about the cause is added, which is the whole of what this may claim.
     *
     * <p>No search was made with those conditions in, so what one would have found is not here to
     * say.
     */
    @Test
    void theOrderSaysWhatWasSearchedAndNotWhyItFailed() {
        String said = only(A_MEASURE_OF_A_COMPARED_POSITION);

        assertTrue(said.contains("which does not make it unreachable"),
                () -> "an empty search is still not a point nothing can be written at: " + said);
    }

    /**
     * And a point whose search was over everything the point asks opens the way it did, which is
     * what makes the order above worth reading.
     */
    @Test
    void aSearchThatLeftNothingOutOpensOnItsOwnWord() {
        List<String> said = whereNothingCouldShowARow(THE_WAY_WAS_USED_WHOLE);

        assertFalse(said.isEmpty(), "this model has points nothing composed a row for");
        for (String each : said) {
            assertTrue(each.contains("— nothing composed one:"),
                    () -> "the opening is the search's own: " + each);
            assertFalse(each.contains(LEFT_OUT),
                    () -> "and the way to it was used whole: " + each);
        }
    }

    private static String only(String model) {
        List<String> said = whereNothingCouldShowARow(model);
        assertFalse(said.isEmpty(), "this model has points nothing composed a row for");
        return said.get(0);
    }

    /** The point lines of the page that say a search came to nothing. */
    private static List<String> whereNothingCouldShowARow(String model) {
        List<String> found = new ArrayList<>();
        for (String line : human(model).split("\n")) {
            if (line.contains("nothing composed one") || line.contains(LEFT_OUT)) {
                found.add(line);
            }
        }
        return found;
    }

    private static String human(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
