package souther.compiler.report;

import souther.compiler.report.AdequacyReport;
import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import static org.junit.jupiter.api.Assertions.assertFalse;
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
        compilation.measure(Adequacy.Asked.fullReport());
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

    /**
     * A position the walk reached, whose rules it did not.
     *
     * <p>What a list holds is a position, and nothing this reading does places a rule at it. The
     * elements a combinator hands a closure are named where the operation still stands, so a
     * comparison written inside one is read; a relation stated of every element by an
     * {@code invariant} is held as a quantifier over the clause and is not, and the model below has
     * only the second. So the word is the one for a position whose rules were never arrived at, and
     * not the one for values held inside something the walk does not reach into: the reaching was
     * made.
     *
     * <p>This model used to carry {@code unsupported_traversal}, and it was the only model here
     * that did. What is left carrying that word is an {@code Option} and a {@code Map}, and no
     * model written here reaches it through either: an optional divides into its two cases and is
     * measured, and a map's contents are named by nothing a body can write that this reads. So the
     * word goes uncarried by any document this test builds until those two are reached into, and
     * what still holds it to meaning one thing is the projection that writes it
     * ({@link souther.compiler.partition.ReportedReason}), tested where that is.
     */
    @Test
    void aPositionWhoseRulesTheReadingNeverArrivedAtIsWrittenAsThatWord() {
        String json = reportOf("""
                module demo
                data Ok
                data Item = { charge: Int }
                data Basket = List<Item>
                    invariant List.all(i -> i.charge >= 1, value)
                behavior run : (items: Basket) -> Ok
                let run (items) = Ok
                """);

        assertTrue(json.contains("\"rules_not_read_at_all\""), json);
        assertFalse(json.contains("\"unsupported_traversal\""), json);
    }
}
