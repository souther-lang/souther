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

    private static final String COMMANDS =
            "/META-INF/souther-docs/cli/commands.md";

    private static String said(CompositionRepertoire... these) {
        return Reasons.writes(PublicationOrders.COMPOSITION_REPERTOIRES.keep(Set.of(these)));
    }

    @Test
    void theReportSaysThePopulationTheSearchWrites() {
        assertEquals(RowsARunIsTriedFor.population(),
                said(CompositionRepertoire.ROWS_A_RUN_IS_TRIED_FOR));
    }

    /** The sentence names the edge and the values, and claims no element rule that only a list has. */
    @Test
    void thePopulationNamesItsFiguresAndNoRuleOfOneContainer() {
        String said = RowsARunIsTriedFor.population();
        assertTrue(said.contains("from 0 to 6"), said);
        assertTrue(said.contains("(0, 1, -1, 2)"), said);
        for (String kind : new String[] {"lists", "sets", "maps", "strings"}) {
            assertTrue(said.contains(kind), kind + " in: " + said);
        }
        assertFalse(said.contains("copies"), said);
        assertFalse(said.contains("plain value"), said);
    }

    /**
     * Read among other populations it is one item: past the comma every population of this kind
     * has after what it is a population of, its own commas are inside the parentheses.
     */
    @Test
    void theSentenceIsOneItemOfACommaSeparatedList() {
        String joined = said(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD,
                CompositionRepertoire.ROWS_A_RUN_IS_TRIED_FOR);
        String ours = RowsARunIsTriedFor.population();
        assertTrue(joined.endsWith(", " + ours), joined);
        assertEquals(2, ours.replaceAll("\\([^)]*\\)", "").split(", ").length, ours);
    }

    /** The command reference states the population the report does. */
    @Test
    void theCommandReferenceStatesThePopulation() throws IOException {
        try (InputStream in = getClass().getResourceAsStream(COMMANDS)) {
            assertNotNull(in, COMMANDS);
            String text = new String(in.readAllBytes(), StandardCharsets.UTF_8)
                    .replaceAll("\\s+", " ");
            Matcher edge = Pattern.compile("from 0 to \\d+")
                    .matcher(RowsARunIsTriedFor.population());
            Matcher values = Pattern.compile("\\(\\d[^)]*\\)")
                    .matcher(RowsARunIsTriedFor.population());
            assertTrue(edge.find() && values.find(), RowsARunIsTriedFor.population());
            assertTrue(text.contains(edge.group()), "the largest container: " + edge.group());
            assertTrue(text.contains(values.group()), "the whole numbers: " + values.group());
            assertTrue(text.contains("lists, sets, maps, strings"), "the containers");
        }
    }
}
