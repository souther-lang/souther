package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A module's rows are written across its own source and any number of attached {@code examples for}
 * files, so what they cover is a question about the module and not about a file.
 *
 * <p>Asked per source, a case covered by the attached file would be reported as uncovered by the
 * module's own — and the author, reading the module's file, would be told to write a row that already
 * exists somewhere else.
 */
class WitnessAcrossSourcesTest {

    private static final String MODEL = """
            module example.trip

            data Amount = Int
                invariant value >= 0

            data Draft = { cost: Amount }
            data Submitted = { cost: Amount }
            data Rejected = { reason: String }

            behavior submit : (request: Draft) -> Submitted | Rejected
                constructs Submitted, Rejected

            let submit (request) = {
                guard request.cost.value <= 100 else Rejected { reason = "over" }
                Submitted { cost = request.cost }
            }
            """;

    private static List<String> names(Set<TypeSymbol> cases) {
        return cases.stream().map(TypeSymbol::name).sorted().toList();
    }

    @Test
    void casesCoveredByAnAttachedFileCountForTheModule() {
        Map<String, String> documents = new LinkedHashMap<>();
        documents.put("trip.sou", MODEL + """

                example submit
                    | "one this file writes" : (Draft { cost = Amount(50) }) -> Submitted
                """);
        documents.put("trip-examples.sou", """
                examples for example.trip

                example submit
                    | "one the attached file writes" : (Draft { cost = Amount(500) })
                        -> Rejected { reason = "over" }
                """);

        Compilation compilation = Compilation.ofDocuments(documents, Set.of(), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(Map.of(), compilation.diagnostics().entrySet().stream()
                        .filter(e -> !e.getValue().isEmpty())
                        .collect(java.util.stream.Collectors.toMap(Map.Entry::getKey,
                                Map.Entry::getValue)),
                "the model under test compiles, so an empty result means the measure and not the model");

        Map<String, Adequacy.SignatureEvidence> witnesses =
                compilation.db().ask(new Adequacy.Witnesses("example.trip")).value();
        assertNotNull(witnesses);
        Adequacy.SignatureEvidence submit = witnesses.get("submit");

        assertEquals(List.of("Rejected", "Submitted"), names(submit.output().seen().specified()),
                "both files' rows are the module's rows");
        assertEquals(List.of(), submit.output().unspecified(),
                "nothing is missing once the two sources are read together");
        assertEquals(List.of("Rejected", "Submitted"), names(submit.output().seen().verified()));
    }
}
