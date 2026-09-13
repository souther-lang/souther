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
 * A point whose row was composed without one of its own demands opens on that, and the word the
 * search came back with follows it.
 *
 * <p>The search's word is about what was tried; that a demand standing where the row is already
 * being written was never brought into the composing is about what was tried <em>with</em>. Opened
 * on the word alone, a reader is told a search had everything and reached nothing, and goes looking
 * for a row nothing can write — where what happened is that no search of the whole thing was ever
 * made.
 *
 * <p><b>Coverage and not cause.</b> Nothing here composed with that demand in, so what such a
 * search would have found is not something this knows. The opening says what was searched; the
 * sentence after it keeps saying that an empty search does not make the point unreachable.
 */
class APointComposedWithoutOneOfItsDemandsSaysSoFirstTest {

    /** The comparison's positions and the condition above the line meet at `b`. */
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

    /** The same shape where both demands are numbers taken of one location on one carrier. */
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

    /**
     * A point nothing composed a row for with no demand left out, which is the control.
     *
     * <p>Its search came back with a word of its own and the way to it was used whole, so the
     * opening this adds would be one written for a search that was over everything the point asks.
     */
    private static final String NOTHING_WAS_LEFT_OUT = """
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

    private static final String OPENS_ON_WHAT_WAS_SEARCHED =
            "nothing was composed against every demand at one of its locations";

    @Test
    void aDemandAtTheRowsOwnLocationIsSaidBeforeTheSearchesWord() {
        List<String> said = whereNothingCouldShowARow(A_MEASURE_OF_A_COMPARED_POSITION);

        assertEquals(1, said.size(), () -> "one point of this model came to nothing: " + said);
        assertTrue(said.get(0).contains("— " + OPENS_ON_WHAT_WAS_SEARCHED + ":"),
                () -> "the opening says what the composing was over: " + said.get(0));
        assertTrue(said.get(0).indexOf(OPENS_ON_WHAT_WAS_SEARCHED)
                        < said.get(0).indexOf("was seen reaching it"),
                () -> "and the search's own word follows it: " + said.get(0));
    }

    /**
     * And nothing about the cause is added, which is the whole of what this may claim.
     *
     * <p>No search was made with that demand in, so what one would have found is not here to say.
     * The sentence that keeps the point open stays where it was.
     */
    @Test
    void theOpeningSaysWhatWasSearchedAndNotWhyItFailed() {
        String said = whereNothingCouldShowARow(A_MEASURE_OF_A_COMPARED_POSITION).get(0);

        assertTrue(said.contains("which does not make it unreachable"),
                () -> "an empty search is still not a point nothing can be written at: " + said);
        assertTrue(said.contains("a condition on another number taken where this row is already"
                        + " being written for one"),
                () -> "and which condition it was is still named: " + said);
    }

    /**
     * The same of a model whose two demands are on one carrier, because what the opening is about
     * is the location being one and not the carriers differing.
     */
    @Test
    void itIsSaidOfTwoNumbersTakenOfOneLocationToo() {
        List<String> said = whereNothingCouldShowARow(TWO_MEASURES_OF_ONE_LOCATION);

        assertFalse(said.isEmpty(), "this model has points nothing composed a row for");
        for (String each : said) {
            assertTrue(each.contains(OPENS_ON_WHAT_WAS_SEARCHED),
                    () -> "every one of them was composed without the condition above it: " + each);
        }
    }

    /**
     * And a point whose search was over everything the point asks opens the way it did, which is
     * what makes the opening above worth reading.
     */
    @Test
    void aSearchThatLeftNoDemandOutOpensOnItsOwnWord() {
        List<String> said = whereNothingCouldShowARow(NOTHING_WAS_LEFT_OUT);

        assertFalse(said.isEmpty(), "this model has points nothing composed a row for");
        for (String each : said) {
            assertTrue(each.contains("— nothing composed one:"),
                    () -> "the opening is the search's own: " + each);
            assertFalse(each.contains(OPENS_ON_WHAT_WAS_SEARCHED),
                    () -> "and no demand of this row was left out of the composing: " + each);
        }
    }

    /** The point lines of the page that say a search came to nothing. */
    private static List<String> whereNothingCouldShowARow(String model) {
        List<String> found = new ArrayList<>();
        for (String line : human(model).split("\n")) {
            if (line.contains("nothing composed one")
                    || line.contains(OPENS_ON_WHAT_WAS_SEARCHED)) {
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
