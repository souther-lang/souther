package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.CameToNothing;
import souther.compiler.partition.CompositionAccount;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.CompositionShortfall;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.Generator;
import souther.compiler.publish.PublicationOrders;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.DecisionEvidence;
import souther.compiler.query.RuleRequirement;
import souther.compiler.query.RuleSearch;
import souther.compiler.query.RuleSettlement;
import souther.compiler.query.SettledAcross;
import souther.compiler.query.SettledAt;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A rule stated at several places says what each of them came to, where a report says the rule.
 *
 * <p>Each place is searched along its own way, and what one search came to is not what another's
 * did. The document names a rule and not its places, so it says every place's answer of the rule;
 * the page counts a rule the model leaves no row once, with what left each place none.
 *
 * <p>Put to the places directly. Nothing this compiler reads yet states one rule at two places, so
 * the second place is a real way of a compiled body standing under the first one's rule, which is
 * the shape the type admits and every reader of a rule has to answer for.
 */
class ARuleSaysWhatEachOfItsPlacesCameToTest {

    private static final String MODEL = """
            module example.placed

            data X
            data Y
            data A = X | Y

            behavior f : (a: A) -> Int

            let f (a) = match a with
                | X -> 1
                | Y -> 2
            """;

    /** Every place's word is in the document, the requirement's own first, each once. */
    @Test
    void theDocumentSaysHowEveryPlaceCameToItsAnswer() {
        List<DecisionReading.Ruled> at = twoPlaces();
        SettledAt elsewhere = new SettledAt(at.get(0), RuleSettlement.of(
                new RuleRequirement.Unsettled.AComposedRowWentElsewhere(),
                CompositionAccount.NOTHING), Set.of());
        SettledAt nothing = new SettledAt(at.get(1), nothingTried(
                CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS), Set.of());

        assertEquals(List.of("a_composed_row_went_elsewhere", "nothing_was_composed_to_try"),
                AdequacyReport.becauseOf(new SettledAcross(List.of(elsewhere, nothing))),
                "the second place had nothing to try, and the document says so of the rule");
        assertEquals(List.of("nothing_was_composed_to_try"),
                AdequacyReport.becauseOf(new SettledAcross(List.of(nothing, nothing))),
                "and a word two places came to is said once");
    }

    /**
     * What every place that had nothing to try met is in the document, joined as the document
     * shows it: two places that stopped at two figures are one word holding both.
     */
    @Test
    void theDocumentSaysWhatEveryPlaceMet() {
        List<DecisionReading.Ruled> at = twoPlaces();
        SettledAcross rule = new SettledAcross(List.of(
                new SettledAt(at.get(0), nothingTried(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS),
                        Set.of()),
                new SettledAt(at.get(1),
                        nothingTried(CompositionBudget.CHARACTERS_A_PROPOSAL_HOLDS), Set.of())));

        List<RuleSearch.Came> said = RuleSearch.Came.joinedAsShown(
                AdequacyReport.shortfallsOf(rule), AdequacyReport::shownInTheDocument);

        assertEquals(1, said.size(), () -> "one word, said once: " + said);
        assertEquals(PublicationOrders.COMPOSITION_BUDGETS.keep(Set.of(
                        CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS,
                        CompositionBudget.CHARACTERS_A_PROPOSAL_HOLDS)),
                said.get(0).figures(), "holding the figure each place stopped at");
    }

    /** The page counts a rule once, where its answer is, with what left each of its places none. */
    @Test
    void thePageSaysWhatLeftEachPlaceNoRow() {
        AdequacyReport.Said first = new AdequacyReport.Said(4, 0, "one reason");
        AdequacyReport.Said second = new AdequacyReport.Said(5, 0, "another reason");

        assertEquals(new AdequacyReport.Said(4, 0, "one reason; another reason"),
                AdequacyReport.everyReason(List.of(first, second)),
                "both reasons, counted where the first is");
        assertEquals(first, AdequacyReport.everyReason(List.of(first, first)),
                "and a reason two places share is said once");
    }

    /** A search of the rule that stopped at {@code figure} with nothing to try. */
    private static RuleSettlement nothingTried(CompositionBudget figure) {
        return RuleSettlement.nothingToTryWith(RuleSearch.CameToNothing.of(List.of(
                        new CameToNothing(new Generator.UnresolvedCombination(
                                List.of("a rule of the decision"),
                                Generator.UnresolvedCombination.Reason.wordFor(Set.of(figure))),
                                CompositionShortfall.of(Set.of(figure)), Set.of()))),
                CompositionAccount.NOTHING);
    }

    /** One rule of the compiled body at two places: its own, and a second way standing under it. */
    private static List<DecisionReading.Ruled> twoPlaces() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        DecisionEvidence decided = compilation.db()
                .ask(new Adequacy.Decides(compilation.modules().getFirst())).value().get("f");
        DecisionReading.Ruled first = decided.read().found().get(0);
        DecisionReading.Ruled other = decided.read().found().get(1);
        return List.of(first, new DecisionReading.Ruled(first.rule(), other.steps(),
                other.whole()));
    }
}
