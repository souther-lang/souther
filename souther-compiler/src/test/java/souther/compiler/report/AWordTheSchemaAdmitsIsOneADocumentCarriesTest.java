package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The two words this branch added to the published vocabulary, in a document.
 *
 * <p>The schema says which words a {@code notDerivable} reason may be, and a test next door holds
 * that list against the enum it spells. Neither of them says a word is ever written: a vocabulary
 * and a document are different things, and a word promised by one and emitted by neither is what
 * that test was written after.
 *
 * <p>So these are the two models the words are for, taken to the document a build reads. A
 * declaration reachable from itself is a type this could not work out; a threshold on a list's
 * elements is values held inside something the walk does not reach into. Both compile, which is why
 * a report is asked about them at all.
 *
 * <p>The version is unchanged by their arrival, and the schema says why in its own words: a word
 * added to an enumerated field is one no earlier document carried, so a document written before it
 * existed is still a document of this version.
 */
class AWordTheSchemaAdmitsIsOneADocumentCarriesTest {

    private static String reportOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).json(SourceNameResolver.identity());
    }

    @Test
    void aTypeThisCouldNotWorkOutIsWrittenAsThatWord() {
        String json = reportOf("""
                module demo
                data Ok
                data Cyclic = Cyclic
                behavior run : (x: Cyclic) -> Ok
                let run (x) = Ok
                """);

        assertTrue(json.contains("\"type_unresolved\""), json);
    }

    @Test
    void valuesHeldInsideSomethingUnreachedAreWrittenAsThatWord() {
        String json = reportOf("""
                module demo
                data Ok
                data Item = { charge: Int }
                behavior run : (items: List<Item>) -> Ok
                let run (items) =
                    { guard List.length(List.filter((i) -> i.charge >= 21000, items)) < 1 else Ok
                      Ok }
                """);

        assertTrue(json.contains("\"unsupported_traversal\""), json);
    }
}
