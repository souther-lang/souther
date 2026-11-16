package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
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
 * case holds a code point that is not whitespace, so a business case holding none is the guard's
 * and no run gets it to the relation between the two strings. The relation is asked of the
 * business cases that do, and leaves none open: each of them is inside the lowercase of some need,
 * so it tells none of them apart.
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

        static final Compilation MODEL = ACompiledModel.measured(PROPOSES,
                Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));

        /** The report, built once: it is the same document for every test. */
        static final String JSON = AdequacyReport.of(MODEL)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    /** The business case is read whole, and a need is not shown reached. */
    @Test
    void theBusinessCaseIsReadWholeAndANeedIsNotShownToReachEveryNeed() {
        String json = Measured.JSON;
        assertFalse(Pattern.compile(SHOWN.formatted(Pattern.quote("businessCase")),
                Pattern.DOTALL).matcher(json).find(), "the business case is shown over no region");
        assertFalse(Pattern.compile(NOT_SHOWN.formatted(Pattern.quote("businessCase")),
                Pattern.DOTALL).matcher(json).find(), "and is not named not shown");
        // A need may be any string: written after with starters, each is inside some business
        // case and outside another, and the empty one is inside every one, which no class says.
        assertTrue(Pattern.compile(NOT_SHOWN.formatted(Pattern.quote("opp.needs[*]")),
                Pattern.DOTALL).matcher(json).find(), "a need is not shown reached");
    }

    /** The business cases holding no code point that is not whitespace are the guard's, and the
     *  relation leaves none of them open. */
    @Test
    void theBusinessCasesHoldingNoneAreNotLeftOpenByTheRelation() {
        String json = Measured.JSON;
        assertFalse(json.contains("not_whitespace"), "no value is open for how many it holds");
        assertFalse(json.contains("\"leftOpen\""), "nothing is left open");
    }

    /** Every business case the guard lets the run get to is inside some need, so the relation
     *  parts none of them and no class is drawn at the place. */
    @Test
    void noClassIsDrawnAtTheBusinessCase() {
        Compilation compilation = ACompiledModel.compiles(Measured.MODEL);
        var evidence = compilation.db().ask(new Adequacy.Coverage("cases")).value()
                .get("propose");
        assertTrue(evidence.axes().stream().noneMatch(axis ->
                axis.path().equals("businessCase") && !axis.classes().isEmpty()),
                () -> "businessCase has a class: " + evidence.axes());
    }
}
