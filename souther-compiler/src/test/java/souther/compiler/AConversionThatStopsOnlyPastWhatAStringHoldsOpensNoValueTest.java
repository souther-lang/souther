package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.StopPastTheRepresentation;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A conversion ends a run where its answer is longer than a {@code String} holds, which is where
 * the representation stops and no distinction a model made. So no value of a relation after it is
 * open for that, however long a string the model leaves the place, and the stop is said once, of
 * the conversion.
 */
class AConversionThatStopsOnlyPastWhatAStringHoldsOpensNoValueTest {

    private static String lengthAndEquality(String conversion, String type) {
        return """
                module b1

                data S = String
                    invariant %s

                behavior f : (email: S, emails: List<S>) -> Int
                let f (email, emails) =
                    String.length(%s(email.value))
                        + List.length(List.filter(own -> own.value == email.value, emails))

                example f
                    | "match" : (S("ab"), [ S("ab") ]) -> 3
                    | "none" : (S("ab"), [ S("cd") ]) -> 2
                """.formatted(type, conversion);
    }

    private static List<String> stops(String source) {
        return WhereAStringRelationIsLeftOpen.evidenceOf(source, "f")
                .stopsPastTheRepresentation().stream()
                .map(StopPastTheRepresentation::operation).toList();
    }

    /** Any string may hold a code point a conversion answers with two, and no value is open for
     *  it: the relation is read over every string, and the conversion is said to stop a run. */
    @Test
    void aConversionOfAStringOfAnyLengthOpensNoValueAndIsSaidOnce() {
        for (String conversion : List.of("String.lowercase", "String.uppercase")) {
            String source = lengthAndEquality(conversion, "String.length(value) >= 0");

            assertEquals(Map.of(), WhereAStringRelationIsLeftOpen.leftOpen(source, "f"),
                    conversion);
            assertEquals(List.of(conversion), stops(source), conversion);
        }
    }

    /** The report says it in the partition of the behavior, in words and in the document. */
    @Test
    void theStopIsSaidInTheReportOfTheBehavior() {
        Compilation compilation = ACompiledModel.measured(
                lengthAndEquality("String.lowercase", "String.length(value) >= 0"),
                Adequacy.Asked.fullReport());
        AdequacyReport report = AdequacyReport.of(compilation);
        String human = report.humanInEnglish(
                SourceRendering.namedByIdentity(compilation.texts()));
        String json = report.json(SourceRendering.namedByIdentity(SourceLayouts.NONE));

        assertTrue(human.lines().anyMatch(line -> line.contains("a run stops only where")
                && line.contains("String.lowercase@")), human);
        assertTrue(json.contains("\"stopsPastTheRepresentation\""), json);
        assertTrue(!json.contains("notShownGottenPast"), json);
    }

    /** A body with no operation that stops past the representation says nothing of one. */
    @Test
    void aBodyWithNoSuchOperationSaysNone() {
        assertEquals(List.of(), stops(lengthAndEquality("String.trim",
                "String.length(value) >= 0")));
    }
}
