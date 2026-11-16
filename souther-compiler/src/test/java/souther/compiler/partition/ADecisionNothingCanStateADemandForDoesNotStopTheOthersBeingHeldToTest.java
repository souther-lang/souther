package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A combination of decisions is held to what can be read of them, and a decision no demand can be
 * read for is left to the run rather than keeping the others from being held to anything. In
 * the human-resources example, the filters of a list whose arms state no demand stood beside an age
 * the classes cannot place, and the age was never looked for.
 */
class ADecisionNothingCanStateADemandForDoesNotStopTheOthersBeingHeldToTest {

    private static final HeldOutcome.Bringing UNREAD = new HeldOutcome.Bringing.NothingFound();

    /** One decision with a demand beside one without. */
    @Test
    void theDecisionsADemandCanBeReadForAreHeldToWhateverStandsBesideThem() {
        HeldOutcome.Bringing read = new HeldOutcome.Bringing.Found(List.of(aWay()), Set.of());

        assertEquals(List.of(read), ReadableDemands.of(List.of(UNREAD, read)).readable());
    }

    @Test
    void theFiguresThatLeftADecisionUnlookedAtCutThePlanAndAskNothingOfARow() {
        ReadableDemands asked = ReadableDemands.of(List.of(new HeldOutcome.Bringing.LeftUnlooked(
                Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG))));

        assertEquals(Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG), asked.cutShort());
        assertTrue(asked.readable().isEmpty());
    }

    /** No value on a side one decision comes out on is read, and not left to the run: it is what
     *  says no row holds the decisions together. */
    @Test
    void noValueOnASideADecisionComesOutOnIsReadBesideTheOthers() {
        HeldOutcome.Bringing read = new HeldOutcome.Bringing.Found(List.of(aWay()), Set.of());
        HeldOutcome.Bringing none = new HeldOutcome.Bringing.NoValueCanStandThere();

        assertEquals(List.of(read, none), ReadableDemands.of(List.of(read, none)).readable());
    }

    /** One way of holding a row, to a truth of {@code open}, over nothing on the way. */
    private static HeldOutcome aWay() {
        return new HeldOutcome(List.of(new RowDemand.ATruth(TermPath.of("open"), true)),
                List.of(), WayToTheBorder.UNTOUCHED, Map.of(), Reachability.untouched(region()));
    }

    private static SearchRegion region() {
        Compilation compilation = ACompiledModel.answered("""
                module m

                behavior f : (open: Bool) -> Int
                let f (open) = if open then 1 else 0
                """);
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Map<String, InputDomain> inputs =
                compilation.db().ask(new Adequacy.Inputs(module)).value();
        return inputs.get("f").reading(rules).quantities().region();
    }
}
