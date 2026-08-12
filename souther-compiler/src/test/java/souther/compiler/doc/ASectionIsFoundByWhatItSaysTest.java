package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/** Search is over what a section says — title and body — not only over its anchor. */
class ASectionIsFoundByWhatItSaysTest {

    private final SpecDocument spec = SpecDocument.of("""
            = A Specification

            [#greeting]
            == Greeting

            A polite word at the boundary.

            [#farewell]
            == Farewell

            The last word, also polite.

            [#farewell-detail]
            === Detail

            Only procedure.
            """);

    @Test
    void searchFindsEverySectionWhoseTitleOrBodyContainsTheTerm() {
        List<SpecDocument.Section> hits = spec.search("polite");

        assertEquals(List.of("greeting", "farewell"),
                hits.stream().map(SpecDocument.Section::anchor).toList());
    }

    @Test
    void aTermSaidOnlyInASubsectionAnswersTheSubsectionAndNotItsParent() {
        List<SpecDocument.Section> hits = spec.search("procedure");

        assertEquals(List.of("farewell-detail"),
                hits.stream().map(SpecDocument.Section::anchor).toList(),
                "the parent's body spans its subsections, but search charges each word to the section that says it");
    }

    @Test
    void searchIsCaseInsensitive() {
        List<SpecDocument.Section> hits = spec.search("FAREWELL");

        assertTrue(hits.stream().map(SpecDocument.Section::anchor).toList().contains("farewell"));
    }

    @Test
    void searchWithNoMatchAnswersAnEmptyList() {
        assertEquals(List.of(), spec.search("impolite"));
    }
}
