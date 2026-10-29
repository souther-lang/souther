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
 * that decodes the business case trimmed. The length of a trimmed string is a condition on the
 * characters of the string and not on its length, so the relation between the two strings is not
 * shown, and the report says so at both places rather than drawing classes there or leaving the
 * relation out.
 *
 * <p>Held against the model the repository carries, so that a change that reads the relation moves
 * this with it and says so.
 */
@ReadsTheRepositorysModels
@CheckedInObservation
class TheCrmsBusinessCaseIsNamedUnshownWhereItsGuardTrimsItTest {

    private static final String NOT_SHOWN = "\"path\"\\s*:\\s*\"%s\"[^{}]*\\}\\s*,\\s*\"stopped\"\\s*:"
            + "\\s*\\[\\s*\\{\\s*\"reason\"\\s*:\\s*\"relation_not_shown_to_reach_every_value\"";

    private static final String SHOWN = "\"path\"\\s*:\\s*\"%s\"[^{}]*\\}\\s*,\\s*\"stopped\"\\s*:"
            + "\\s*\\[\\s*\\{\\s*\"reason\"\\s*:\\s*\"relation_shown_over_a_region\"";

    private static Compilation crm() {
        Compilation crm = RepositoryModels.byCorpus().get("crm");
        crm.measure(Adequacy.Asked.fullReport());
        crm.answerEverything();
        return crm;
    }

    /** The relation is named not shown at the needs and at the business case. */
    @Test
    void theRelationIsNamedNotShownAtBothPlaces() {
        String json = AdequacyReport.of(crm())
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
        for (String path : new String[] {"opp.needs[*]", "businessCase"}) {
            assertTrue(Pattern.compile(NOT_SHOWN.formatted(Pattern.quote(path)), Pattern.DOTALL)
                    .matcher(json).find(), () -> path + " is named not shown");
            assertFalse(Pattern.compile(SHOWN.formatted(Pattern.quote(path)), Pattern.DOTALL)
                    .matcher(json).find(), () -> path + " is not shown over a region");
        }
    }

    /** No class is drawn at either place, so nothing is claimed of the strings there. */
    @Test
    void noClassIsDrawnAtEitherPlace() {
        var evidence = crm().db().ask(new Adequacy.Coverage("example.pipeline")).value()
                .get("proposeValue");
        assertTrue(evidence.axes().stream().noneMatch(axis ->
                axis.path().equals("businessCase") || axis.path().equals("opp.needs[*]")),
                () -> evidence.axes().toString());
    }
}
