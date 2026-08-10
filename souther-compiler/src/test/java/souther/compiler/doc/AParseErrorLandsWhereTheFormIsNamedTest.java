package souther.compiler.doc;

import souther.compiler.diag.DiagnosticCode;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A reader who arrives by a syntax error reaches the form, and not only the rule that refused it.
 *
 * <p>{@code delimiters} holds the places a reading can stop, and a parse code names the one it
 * stopped at. Two of them used to say that a declaration, or an expression, MUST be written in the
 * form given for it and name no place that gives one — so a reader spent the lookup and arrived at
 * the obligation they already knew about. Resolving is not answering, and what a lookup answers
 * with is what this holds.
 *
 * <p>Which places to hold is derived from both ends: the codes are {@link DiagnosticCode}'s, and a
 * place is one whose anchor turns out to stand in that section. Neither side is a list kept here.
 *
 * <p>Only that is held. That a code's anchor resolves at all, and that no two codes share one, are
 * {@code EveryDiagnosticCodeIsReadableTest}; that every cross-reference in the document can be
 * asked for is {@code EveryNameTheSpecificationSendsAReaderToCanBeAskedForTest}; and whether the
 * language's forms are covered at all is the inventory in {@code grammar}.
 */
class AParseErrorLandsWhereTheFormIsNamedTest {

    private static final String WHERE_A_READING_STOPS = "delimiters";

    @Test
    void everyPlaceAReadingStopsAtNamesWhereItsFormsAreGiven() {
        SpecDocument spec = SpecDocument.bundled();
        SpecDocument.Section stops = spec.section(WHERE_A_READING_STOPS);
        List<String> held = new ArrayList<>();
        List<String> silent = new ArrayList<>();

        for (DiagnosticCode code : DiagnosticCode.values()) {
            SpecDocument.Section landing = spec.section(code.ruleAnchor());
            if (landing == null || !landing.anchor().equals(stops.anchor())) {
                continue;
            }
            held.add(code.name());
            if (!lineCarrying(stops.body(), code.ruleAnchor()).contains("<<")) {
                silent.add(code.name() + " (" + code.ruleAnchor() + ")");
            }
        }

        assertFalse(held.isEmpty(), "no code stops in `" + WHERE_A_READING_STOPS + "` at all");
        assertEquals(List.of(), silent, "these stop a reading and name nowhere the form is given");
    }

    /** The one line of {@code body} carrying {@code [[anchor]]} — the place's own sentence. */
    private static String lineCarrying(String body, String anchor) {
        return body.lines()
                .filter(line -> line.contains("[[" + anchor + "]]"))
                .findFirst()
                .orElseThrow(() -> new AssertionError(
                        "`" + anchor + "` resolves into the section but is written nowhere in it"));
    }
}
