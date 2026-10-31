package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior reads a business case against the needs recorded, after a guard that decodes the
 * business case trimmed. What the trimmed string leaves is something exactly where the business
 * case holds a code point that is not whitespace, so the relation between the two strings is shown
 * over the business cases that do, and the report says which are left open: those holding none.
 *
 * <p>Measured at {@code witness}: what is read here is how the positions divide and why a relation
 * stops, and none of it turns on a value composed at a line.
 */
class ABusinessCaseIsReadPastTheGuardThatTrimsItTest {

    private static final String PROPOSES = """
            module cases exposing ( BusinessCase, Need, Needs, Opp, Pitch, Misses, propose )

            data BusinessCase = String invariant String.length(value) >= 1
            data Need = String
            data Needs = List<Need> invariant List.length(value) >= 1
            data Opp = { needs: Needs }
            data Pitch = { businessCase: BusinessCase }
            data Misses

            behavior propose : (opp: Opp, businessCase: String) -> Pitch | Misses
                constructs Pitch, BusinessCase

            let answersANeed (businessCase: String, Needs(points)): Bool =
                List.any(p -> String.contains(String.lowercase(p.value),
                                              String.lowercase(businessCase)), points)

            let propose (opp, businessCase) = {
                guard BusinessCase(String.trim(businessCase)) as stated else Misses
                guard answersANeed(businessCase, opp.needs) else Misses
                Pitch { businessCase = stated }
            }
            """;

    private static final String SHOWN = "\"path\"\\s*:\\s*\"%s\"[^{}]*\\}\\s*,\\s*\"stopped\"\\s*:"
            + "\\s*\\[\\s*\\{\\s*\"reason\"\\s*:\\s*\"relation_shown_over_a_region\"";

    private static final String NOT_SHOWN = "\"path\"\\s*:\\s*\"%s\"[^{}]*\\}\\s*,\\s*\"stopped\"\\s*:"
            + "\\s*\\[\\s*\\{\\s*\"reason\"\\s*:\\s*\"relation_not_shown_to_reach_every_value\"";

    /** The model measured once for every test here, which only read what it came to. */
    private static final class Measured {

        static final Compilation MODEL = measure();

        /** The report, built once: it is the same document for every test. */
        static final String JSON = AdequacyReport.of(MODEL)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));

        private static Compilation measure() {
            Compilation model = Compilation.ofSource(PROPOSES, "Main");
            model.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
            model.answerEverything();
            if (!model.errors().isEmpty()) {
                throw new IllegalStateException("the model compiles: " + model.errors().stream()
                        .map(e -> e.diagnostic().code() + " " + e.diagnostic().titleKey()).toList());
            }
            return model;
        }
    }

    /** The relation is shown over a region at the needs and at the business case. */
    @Test
    void theRelationIsShownOverARegionAtBothPlaces() {
        String json = Measured.JSON;
        for (String path : new String[] {"opp.needs[*]", "businessCase"}) {
            assertTrue(Pattern.compile(SHOWN.formatted(Pattern.quote(path)), Pattern.DOTALL)
                    .matcher(json).find(), () -> path + " is shown over a region");
            assertFalse(Pattern.compile(NOT_SHOWN.formatted(Pattern.quote(path)), Pattern.DOTALL)
                    .matcher(json).find(), () -> path + " is not named not shown");
        }
    }

    /** The business cases left open are those holding no code point that is not whitespace. */
    @Test
    void theBusinessCasesHoldingNoneAreLeftOpen() {
        String json = Measured.JSON;
        assertTrue(Pattern.compile("\"codePoints\"\\s*:\\s*\\[\\s*\\{\\s*\"class\"\\s*:"
                + "\\s*\"not_whitespace\"\\s*,\\s*\"fewerThan\"\\s*:\\s*1\\s*\\}")
                .matcher(json).find(), "the strings short of a code point that is not whitespace");
    }

    /** A class is drawn at both places, over the strings the guard lets the run get to. */
    @Test
    void aClassIsDrawnAtEachPlace() {
        var evidence = Measured.MODEL.db().ask(new Adequacy.Coverage("cases")).value()
                .get("propose");
        for (String path : new String[] {"businessCase", "opp.needs[*]"}) {
            assertTrue(evidence.axes().stream().anyMatch(axis ->
                    axis.path().equals(path) && !axis.classes().isEmpty()),
                    () -> path + " has a class: " + evidence.axes());
        }
    }
}
