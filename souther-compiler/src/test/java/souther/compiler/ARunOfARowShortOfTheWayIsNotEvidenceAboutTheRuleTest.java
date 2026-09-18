package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.RuleRequirement;
import souther.compiler.query.RuleSearch;
import souther.compiler.query.RuleSettlement;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a row was composed against less than the way states, the rule its run went past is left
 * where it was.
 *
 * <p><b>Whichever side of the way the condition is about.</b> A condition about what a dependency
 * answers and a condition about the input a row writes values at are read by two projections and go
 * unrepresented for reasons of their own, and a row composed without either is a row meeting less
 * than the way states. Read as a run like any other, what it reaches is reported as the model
 * refusing the way it did not reach — which is this compiler's shortfall published as the model's.
 *
 * <p><b>And only the negative.</b> A row that took the rule took it, however it was composed: the
 * run is what says so. What an incomplete row cannot do is stand for the rule having been gone
 * past, and that is the one answer this takes away.
 */
class ARunOfARowShortOfTheWayIsNotEvidenceAboutTheRuleTest {

    /**
     * A body deciding on two records of its own input.
     *
     * <p>A difference between two records is read from end to end and is a distance on nothing, so
     * the way over the input states nothing about it and the demand reading has nothing to say
     * either — the condition is about the input. Nothing is written into the account of the
     * composing by either composer, and what the row was composed without is the walk's own
     * decline.
     */
    private static final String RECORDS_OF_THE_INPUT_COMPARED = """
            module example.inputrecords

            data K = { id: Int }
            data R = { k: K, j: K }
            data Yes
            data No
            data Answer = Yes | No

            behavior decides : (r: R) -> Answer
            let decides (r) = if r.k == r.j then Yes else No
            """;

    /** The rule the composed row did not take is not one this says nothing takes. */
    @Test
    void theRuleARowShortOfTheWayWentPastIsLeftWhereItWas() {
        List<RuleSettlement> settled = settlementsOf(RECORDS_OF_THE_INPUT_COMPARED);

        assertTrue(settled.stream().anyMatch(each ->
                        each.requirement()
                                instanceof RuleRequirement.Unsettled.AComposedRowWasShortOfTheWay),
                () -> "the row was composed without what the way states: " + settled);
        assertFalse(settled.stream().anyMatch(each ->
                        each.requirement()
                                instanceof RuleRequirement.Unsettled.AComposedRowWentElsewhere),
                () -> "so where it went is not read as the rule having been gone past: " + settled);
    }

    /**
     * And the row it was is neither denied nor demoted.
     *
     * <p>Something was composed and tried, which is what the search says; and the rule the run took
     * is stood in by it. Said as a composing that produced no candidate, a reader would be told
     * there was nothing to try the rule with while a row of it was being offered.
     */
    @Test
    void theRowItselfIsStillWhatTheSearchComposedAndRan() {
        List<RuleSettlement> settled = settlementsOf(RECORDS_OF_THE_INPUT_COMPARED);

        for (RuleSettlement each : settled) {
            assertInstanceOf(RuleSearch.Composed.class, each.search(),
                    () -> "a row was composed for every rule of this body: " + each);
        }
        assertTrue(settled.stream().anyMatch(each ->
                        each.requirement() instanceof RuleRequirement.Required),
                () -> "and the rule its run took is stood in by it: " + settled);
    }

    /** What each rule of the body came to. */
    private static List<RuleSettlement> settlementsOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        List<RuleSettlement> out = AdequacyReport.of(compilation).modules().stream()
                .flatMap(module -> module.behaviors().stream())
                .filter(each -> "decides".equals(each.name()))
                .flatMap(each -> each.ruleSettlements().values().stream())
                .toList();
        assertFalse(out.isEmpty(), "the body decides, so it has rules a row is looked for at");
        return out;
    }
}
