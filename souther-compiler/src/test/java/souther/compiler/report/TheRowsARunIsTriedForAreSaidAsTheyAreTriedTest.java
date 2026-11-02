package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.CompositionRepertoire;
import souther.compiler.partition.RowsARunIsTriedFor;
import souther.compiler.publish.PublicationOrders;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the report and the command reference say of the rows a run is tried for is the population
 * the search writes. The search's own population is pinned in {@code
 * EveryRowARunIsTriedForIsTriedTest}; this holds the two places that describe it to that.
 */
class TheRowsARunIsTriedForAreSaidAsTheyAreTriedTest {

    private static final String COMMANDS = "/META-INF/souther-docs/cli/commands.md";

    private static String said(CompositionRepertoire... these) {
        return Reasons.writes(PublicationOrders.COMPOSITION_REPERTOIRES.keep(Set.of(these)));
    }

    /** A point is told only of the axes it was tried at. */
    @Test
    void eachPopulationNamesTheAxesItWasTriedAt() {
        String sizes = said(CompositionRepertoire.ROWS_A_RUN_IS_TRIED_FOR_AT_SIZES);
        assertTrue(sizes.contains("from 0 to 6"), sizes);
        assertFalse(sizes.contains("whole numbers"), sizes);

        String values = said(CompositionRepertoire.ROWS_A_RUN_IS_TRIED_FOR_AT_VALUES);
        assertTrue(values.contains("{0, 1, -1, 2}"), values);
        assertFalse(values.contains("containers"), values);

        String both = said(CompositionRepertoire.ROWS_A_RUN_IS_TRIED_FOR_AT_SIZES_AND_VALUES);
        assertTrue(both.contains("from 0 to 6") && both.contains("{0, 1, -1, 2}"), both);
    }

    /** No sentence claims how a container's elements are written: that is the type's. */
    @Test
    void noSentenceClaimsHowAnElementIsWritten() {
        for (CompositionRepertoire each : CompositionRepertoire.values()) {
            String said = said(each);
            assertFalse(said.contains("copies"), said);
            assertFalse(said.contains("plain value"), said);
        }
    }

    /** Read among other populations a sentence is one item: everything past its noun is in parentheses. */
    @Test
    void theSentenceIsOneItemOfACommaSeparatedList() {
        for (CompositionRepertoire each : Set.of(
                CompositionRepertoire.ROWS_A_RUN_IS_TRIED_FOR_AT_SIZES,
                CompositionRepertoire.ROWS_A_RUN_IS_TRIED_FOR_AT_VALUES,
                CompositionRepertoire.ROWS_A_RUN_IS_TRIED_FOR_AT_SIZES_AND_VALUES)) {
            String ours = said(each);
            String joined = said(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD, each);
            assertTrue(joined.endsWith(", " + ours), joined);
            assertEquals(1, ours.replaceAll("\\([^)]*\\)", "").split(", ").length, ours);
            assertFalse(ours.contains("other than"), ours);
        }
    }

    /** The command reference states the figures the report does. */
    @Test
    void theCommandReferenceStatesThePopulation() throws IOException {
        try (InputStream in = getClass().getResourceAsStream(COMMANDS)) {
            assertNotNull(in, COMMANDS);
            String text = new String(in.readAllBytes(), StandardCharsets.UTF_8)
                    .replaceAll("\\s+", " ");
            Matcher edge = Pattern.compile("from 0 to \\d+").matcher(RowsARunIsTriedFor.sizes());
            Matcher values = Pattern.compile("\\{\\d[^}]*\\}").matcher(RowsARunIsTriedFor.values());
            assertTrue(edge.find() && values.find(), RowsARunIsTriedFor.sizes());
            assertTrue(text.contains(edge.group()), "the largest container: " + edge.group());
            assertTrue(text.contains(values.group()), "the whole numbers: " + values.group());
        }
    }
}
