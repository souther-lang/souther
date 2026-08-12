package souther.compiler.doc;

import souther.compiler.diag.DiagnosticCode;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A reader who arrives by a syntax error reaches the form, and not only the rule that refused it.
 *
 * <p>Two hops, and each is held on its own. A code hands its reader a place the reading can stop,
 * and that place names where the forms it is about are given. Two of the places used to say that a
 * declaration, or an expression, MUST be written in the form given for it and name no place that
 * gives one — so a reader spent the lookup and arrived at the obligation they already knew about.
 * Resolving is not answering.
 *
 * <p>The two sides of the first hop are declared separately, and that is the point of it. The
 * compiler writes out which codes report a text that did not read; the document marks the places it
 * lists as ones a reading stops at. Deriving both from what the codes point at would agree with
 * itself: a code sent off to some other rule would leave the comparison rather than fail it.
 */
class AParseErrorLandsWhereTheFormIsNamedTest {

    private static final String WHERE_A_READING_STOPS = "delimiters";
    private static final String ROLE = "reading-stops";
    /** An anchor written into a list item — {@code [[id]]}, which is how a place is named. */
    private static final Pattern NAMED = Pattern.compile("\\[\\[([a-zA-Z0-9_-]+)]]");

    @Test
    void theCodesAndThePlacesAreOneSet() {
        Set<String> handedToAReader = new TreeSet<>();
        for (DiagnosticCode code : DiagnosticCode.whereAReadingStops()) {
            handedToAReader.add(code.ruleAnchor());
        }
        assertEquals(new TreeSet<>(placesTheDocumentLists().keySet()), handedToAReader,
                "the places a reading stops and the places the codes hand a reader are not the same");
    }

    @Test
    void everyPlaceNamesWhereItsFormsAreGiven() {
        List<String> silent = new ArrayList<>();
        placesTheDocumentLists().forEach((place, said) -> {
            if (!said.contains("<<")) {
                silent.add(place);
            }
        });
        assertEquals(List.of(), silent, "these stop a reading and name nowhere the form is given");
    }

    /** Each place the document lists as one a reading stops at, and the sentence that states it. */
    private static java.util.Map<String, String> placesTheDocumentLists() {
        SpecDocument spec = SpecDocument.bundled();
        SpecDocument.Section stops = spec.section(WHERE_A_READING_STOPS);
        List<String> lines = stops.body().lines().toList();
        int declared = lines.indexOf("[role=\"" + ROLE + "\"]");
        assertTrue(declared >= 0,
                "`" + WHERE_A_READING_STOPS + "` marks no list as the places a reading stops");

        java.util.Map<String, String> places = new java.util.LinkedHashMap<>();
        for (String line : lines.subList(declared + 1, lines.size())) {
            if (!line.startsWith("* ")) {
                break;
            }
            Matcher named = NAMED.matcher(line);
            assertTrue(named.find(), "a place a reading stops at is named, and this one is not: " + line);
            assertTrue(spec.section(named.group(1)) != null,
                    "`" + named.group(1) + "` cannot be asked for");
            places.put(named.group(1), line);
        }
        assertFalse(places.isEmpty(), "the list is marked and holds nothing");
        return places;
    }
}
