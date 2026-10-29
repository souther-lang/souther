package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.conformance.RepositoryModels;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.test.CheckedInObservation;
import souther.test.ReadsTheRepositorysModels;

import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The CRM's {@code proposeValue} reads a business case against the needs recorded, after a guard
 * that decodes the business case trimmed. What the trimmed string leaves is something exactly
 * where the business case holds a code point that is not whitespace, so the relation between the
 * two strings is shown over the business cases that do, and the report says which are left open:
 * those holding none.
 *
 * <p>Held against the model the repository carries, so that a change that reads it differently
 * moves this with it and says so.
 */
@ReadsTheRepositorysModels
@CheckedInObservation
class TheCrmsBusinessCaseIsReadPastTheGuardThatTrimsItTest {

    private static final String SHOWN = "\"path\"\\s*:\\s*\"%s\"[^{}]*\\}\\s*,\\s*\"stopped\"\\s*:"
            + "\\s*\\[\\s*\\{\\s*\"reason\"\\s*:\\s*\"relation_shown_over_a_region\"";

    private static final String NOT_SHOWN = "\"path\"\\s*:\\s*\"%s\"[^{}]*\\}\\s*,\\s*\"stopped\"\\s*:"
            + "\\s*\\[\\s*\\{\\s*\"reason\"\\s*:\\s*\"relation_not_shown_to_reach_every_value\"";

    /** The model measured once for every test here, which only read what it came to. */
    private static final class Measured {

        static final Compilation CRM = measure();

        /** The report, built once: it is the same document for every test. */
        static final String JSON = AdequacyReport.of(CRM)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));

        private static Compilation measure() {
            Compilation crm = RepositoryModels.byCorpus().get("crm");
            crm.measure(Adequacy.Asked.fullReport());
            crm.answerEverything();
            return crm;
        }
    }

    private static Compilation crm() {
        return Measured.CRM;
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
        var evidence = crm().db().ask(new Adequacy.Coverage("example.pipeline")).value()
                .get("proposeValue");
        for (String path : new String[] {"businessCase", "opp.needs[*]"}) {
            assertTrue(evidence.axes().stream().anyMatch(axis ->
                    axis.path().equals(path) && !axis.classes().isEmpty()),
                    () -> path + " has a class: " + evidence.axes());
        }
    }
}
