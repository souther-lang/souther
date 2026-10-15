package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.CameToNothing;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.CompositionCapacity;
import souther.compiler.partition.CompositionRepertoire;
import souther.compiler.partition.CompositionShortfall;
import souther.compiler.partition.Generator;
import souther.compiler.publish.CanonicalSelection;
import souther.compiler.publish.PublicationOrders;
import souther.compiler.query.RuleSearch;

import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every reader that shows less of a word than the word holds says it once for each thing it shows,
 * holding what every word shown alike met.
 *
 * <p>Two searches may come back with words that differ only in what a reader leaves out — the
 * sentence beside the word, or what the search was about. Written as two, the reader says one
 * thing twice with half of the figures apiece. One reader each: the document, the page's line for
 * a rule of a decision, and the two lines of a block of generated rows.
 */
class AReaderSaysOnceWhatItCannotTellApartTest {

    private static final CompositionBudget ELEMENTS = CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS;

    private static final CompositionBudget CHARACTERS =
            CompositionBudget.CHARACTERS_A_PROPOSAL_HOLDS;

    /** The document says the word and its causes, and not the sentence beside the word. */
    @Test
    void theDocumentSaysOneWordWithTwoSentencesOnce() {
        RuleSearch.Came elements = came("one stand-in", null, ELEMENTS);
        RuleSearch.Came characters = came("another stand-in", null, CHARACTERS);

        List<RuleSearch.Came> said = RuleSearch.Came.joinedAsShown(
                List.of(elements, characters), AdequacyReport::shownInTheDocument);

        assertEquals(1, said.size(), () -> "the document cannot tell these two apart: " + said);
        assertEquals(PublicationOrders.COMPOSITION_BUDGETS.keep(Set.of(ELEMENTS, CHARACTERS)),
                said.get(0).figures(),
                "and what either met is held, in the order the document says figures in");
        assertEquals(said.stream().map(RuleSearch.Came::figures).toList(),
                RuleSearch.Came.joinedAsShown(List.of(characters, elements),
                                AdequacyReport::shownInTheDocument).stream()
                        .map(RuleSearch.Came::figures).toList(),
                "whichever of them was met first");
    }

    /** Two words are two entries, however the rest of them reads. */
    @Test
    void theDocumentSaysTwoWordsApart() {
        RuleSearch.Came stood = came("one stand-in", null, ELEMENTS);
        RuleSearch.Came table = new RuleSearch.Came(new Generator.UnresolvedCombination(
                List.of("a rule of the decision"),
                Generator.UnresolvedCombination.Reason.A_TABLE_IS_WHAT_THIS_NEEDS),
                NO_FIGURES, NO_POPULATIONS, NO_CAPACITIES, NO_FIGURES);

        assertEquals(List.of(stood, table), RuleSearch.Came.joinedAsShown(
                        List.of(stood, table), AdequacyReport::shownInTheDocument),
                "two words are two things the document says");
    }

    /**
     * The page says a word's own sentence where it has one, and not what it is about: two words
     * with one sentence and two subjects are one clause with both figures.
     */
    @Test
    void thePageSaysOneSentenceAboutTwoThingsOnce() {
        String said = AdequacyReport.nothingToTry(
                List.of(came("nothing stood in", "one position", ELEMENTS),
                        came("nothing stood in", "another position", CHARACTERS)),
                SourceRendering.namedByIdentity(SourceLayouts.NONE), cited -> null).text();

        assertEquals(1, said.split("nothing stood in", -1).length - 1,
                () -> "the page cannot tell these two apart: " + said);
        assertTrue(said.startsWith(Reasons.met(CompositionShortfall.of(Set.of(ELEMENTS,
                        CHARACTERS)))), () -> "and the clause opens on both figures: " + said);
    }

    /**
     * A block names what a search was about, and two searches of one position for two
     * combinations are one line about that position with both figures.
     */
    @Test
    void aBlockSaysOneLineAboutAPositionOnce() {
        List<CameToNothing> joined = CameToNothing.joinedAsShown(
                List.of(stopped(List.of("a", "b"), "the position", ELEMENTS),
                        stopped(List.of("a", "c"), "the position", CHARACTERS)),
                GeneratedRows::shownForWhatItIsAbout);

        assertEquals(1, joined.size(), () -> "one position, one line: " + joined);
        assertEquals(Set.of(ELEMENTS, CHARACTERS), joined.get(0).met().figures(),
                "holding what both searches met");
    }

    /** And a line named for its finding does not say what the search was about either. */
    @Test
    void aLineNamedForItsFindingSaysOneWordAboutTwoThingsOnce() {
        List<CameToNothing> joined = CameToNothing.joinedAsShown(
                List.of(stopped(List.of("a"), "one position", ELEMENTS),
                        stopped(List.of("a"), "another position", CHARACTERS)),
                GeneratedRows::shownUnderItsFinding);

        assertEquals(1, joined.size(), () -> "the line names the finding, not these: " + joined);
        assertEquals(Set.of(ELEMENTS, CHARACTERS), joined.get(0).met().figures(),
                "holding what both searches met");
    }

    private static RuleSearch.Came came(String said, String about, CompositionBudget figure) {
        return new RuleSearch.Came(new Generator.UnresolvedCombination(
                List.of("a rule of the decision"),
                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE, about,
                Optional.of(said)),
                PublicationOrders.COMPOSITION_BUDGETS.keep(Set.of(figure)), NO_POPULATIONS,
                NO_CAPACITIES, NO_FIGURES);
    }

    private static CameToNothing stopped(List<String> classes, String about,
                                         CompositionBudget figure) {
        return new CameToNothing(new Generator.UnresolvedCombination(classes,
                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE, about,
                Optional.empty()),
                CompositionShortfall.of(Set.of(figure)), Set.of());
    }

    private static final CanonicalSelection<CompositionBudget> NO_FIGURES =
            PublicationOrders.COMPOSITION_BUDGETS.keep(Set.of());

    private static final CanonicalSelection<CompositionRepertoire> NO_POPULATIONS =
            PublicationOrders.COMPOSITION_REPERTOIRES.keep(Set.of());

    private static final CanonicalSelection<CompositionCapacity> NO_CAPACITIES =
            PublicationOrders.COMPOSITION_CAPACITIES.keep(Set.of());
}
