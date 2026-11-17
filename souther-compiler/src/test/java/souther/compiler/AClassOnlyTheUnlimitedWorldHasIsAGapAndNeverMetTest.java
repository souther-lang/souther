package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The sets of a relation between strings are over strings with no greatest length (ADR-0130), so a
 * place a model holds to lengths at the longest a {@code String} holds has values, and none of them
 * is the piece of any value of the other side: the unlimited world gives it a partner and no value
 * can. The class that comes of it is owed a row no value can be written for. That is said as a gap
 * and is never shown met, so the error of the abstraction runs the one way a claim of completeness
 * is safe from.
 */
class AClassOnlyTheUnlimitedWorldHasIsAGapAndNeverMetTest {

    private static final String A_DOMAIN_AS_LONG_AS_A_STRING_GOES = """
            module edge

            data Yes
            data No
            data Email = String
                invariant String.matches("[a-z]+@[a-z]+", value)
            data Domain = String
                invariant String.matches("[a-z]+", value)
                    && String.length(value) == 268435454

            behavior f : (email: Email, domain: Domain) -> Yes | No
            let f (email, domain) =
                match List.get(1, String.split("@", email.value)) with
                    | Some d -> if d == domain.value then Yes else No
                    | None -> No
            """;

    @Test
    void aPlaceHeldToTheLongestLengthIsOwedARowNoValueCanBeWrittenForAndIsNeverMet() {
        Compilation compilation = ACompiledModel.measured(A_DOMAIN_AS_LONG_AS_A_STRING_GOES,
                Adequacy.Asked.fullReport());
        String report = AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));

        assertFalse(report.contains("adequacy: satisfied"), report);
        assertTrue(report.contains("nothing could show a row can be written at a decision rule"),
                report);
        assertTrue(report.contains("how many characters a proposed string holds"), report);
    }
}
