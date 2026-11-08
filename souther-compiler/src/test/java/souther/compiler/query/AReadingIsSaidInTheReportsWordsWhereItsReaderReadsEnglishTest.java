package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Messages;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a reading of a boundary asks of a row is said twice: in the report's words, which are
 * English and which the report keys on, and as the catalog's phrase a diagnostic is told in the
 * reader's language. Both are built from the same parts, and the catalog's English is the report's
 * words: read in English, the phrase is the report's sentence exactly. A change to one wording that
 * left the other behind is what this sees.
 */
class AReadingIsSaidInTheReportsWordsWhereItsReaderReadsEnglishTest {

    /** A line read at a level and in a run, under one case of a value and then the other. */
    private static final String TERM = """
            module example.term

            data OneYear
            data TwoYear
            data Term = OneYear | TwoYear
            data Ok
            data No

            behavior check : (term: Term, month: Int) -> Ok | No

            let limit (t: Term) : Int = match t with
                | OneYear -> 12
                | TwoYear -> 24

            let check (term, month) = {
                guard month <= limit(term) else No
                Ok
            }

            example check
                | (OneYear, 1) -> Ok
            """;

    @Test
    void theCatalogsEnglishIsTheReportsSentence() {
        Compilation compilation = Compilation.ofSource(TERM, "Main");
        List<BorderObligationPointAssessment> points = compilation.db().ask(
                new Adequacy.Obligations("example.term", new GenerationScope.Module(),
                        HowALineIsRead.VALUES_COMPOSED)).value();
        assertNotNull(points, "the model under test compiles");
        WhereTheReadingsDiffer apart = WhereTheReadingsDiffer.of(points);

        List<String> apartFromTheReport = new ArrayList<>();
        int saidWhere = 0;
        for (BorderObligationPointAssessment point : points) {
            for (BorderObligationPointAssessment.ReadingSaid reading : point.readingsSaid(apart)) {
                if (reading.asked() == null) {
                    continue;
                }
                String inEnglish = Messages.text(reading.asked(), Locale.ENGLISH);
                if (!inEnglish.equals(reading.asks())) {
                    apartFromTheReport.add(reading.asks() + " / " + inEnglish);
                }
                if (reading.asks().contains(" where ")) {
                    saidWhere++;
                }
            }
        }
        // The control: the readings include one said under a case of the value, so the words the
        // cases are joined by were compared and not only the relation.
        assertTrue(saidWhere > 0, () -> "a reading under a case of `term`: " + points);
        assertEquals(List.of(), apartFromTheReport,
                "the catalog's English for a reading is not the report's sentence for it");
    }
}
