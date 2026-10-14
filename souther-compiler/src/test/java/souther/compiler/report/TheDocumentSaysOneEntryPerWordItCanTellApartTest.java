package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.CompositionCapacity;
import souther.compiler.partition.CompositionRepertoire;
import souther.compiler.partition.Generator;
import souther.compiler.publish.CanonicalSelection;
import souther.compiler.publish.PublicationOrders;
import souther.compiler.query.RuleSearch;

import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The document says a word the ways of a rule came back with once for everything it can tell
 * apart, holding what each of them met.
 *
 * <p>Two ways may come back with one word and two sentences beside it. The page says both
 * sentences; the document says the word and its causes and not the sentence, so written as two
 * entries the two read as one entry said twice, each with half of what was met.
 */
class TheDocumentSaysOneEntryPerWordItCanTellApartTest {

    @Test
    void oneWordWithTwoSentencesIsOneEntryHoldingBothFigures() {
        RuleSearch.Came elements =
                came("one stand-in", CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS);
        RuleSearch.Came characters =
                came("another stand-in", CompositionBudget.CHARACTERS_A_PROPOSAL_HOLDS);

        List<RuleSearch.Came> said = AdequacyReport.published(List.of(elements, characters));

        assertEquals(1, said.size(), () -> "the document cannot tell these two apart: " + said);
        assertEquals(PublicationOrders.COMPOSITION_BUDGETS.keep(Set.of(
                        CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS,
                        CompositionBudget.CHARACTERS_A_PROPOSAL_HOLDS)),
                said.get(0).figures(),
                "and what either met is held, in the order the document says figures in");
        assertEquals(said.stream().map(RuleSearch.Came::figures).toList(),
                AdequacyReport.published(List.of(characters, elements)).stream()
                        .map(RuleSearch.Came::figures).toList(),
                "whichever of them was met first");
    }

    @Test
    void twoWordsAreTwoEntries() {
        RuleSearch.Came stood = came("one stand-in", CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS);
        RuleSearch.Came table = new RuleSearch.Came(new Generator.UnresolvedCombination(
                List.of("a rule of the decision"),
                Generator.UnresolvedCombination.Reason.A_TABLE_IS_WHAT_THIS_NEEDS),
                PublicationOrders.COMPOSITION_BUDGETS.keep(Set.of()), NO_POPULATIONS,
                NO_CAPACITIES);

        assertEquals(List.of(stood, table), AdequacyReport.published(List.of(stood, table)),
                "two words are two things the document says");
    }

    private static RuleSearch.Came came(String said, CompositionBudget figure) {
        return new RuleSearch.Came(new Generator.UnresolvedCombination(
                List.of("a rule of the decision"),
                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE, null,
                Optional.of(said)),
                PublicationOrders.COMPOSITION_BUDGETS.keep(Set.of(figure)), NO_POPULATIONS,
                NO_CAPACITIES);
    }

    private static final CanonicalSelection<CompositionRepertoire> NO_POPULATIONS =
            PublicationOrders.COMPOSITION_REPERTOIRES.keep(Set.of());

    private static final CanonicalSelection<CompositionCapacity> NO_CAPACITIES =
            PublicationOrders.COMPOSITION_CAPACITIES.keep(Set.of());
}
