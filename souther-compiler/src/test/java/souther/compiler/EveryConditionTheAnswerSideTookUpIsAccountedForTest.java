package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.ConditionReportAnchor;
import souther.compiler.partition.DemandGap;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.RuleSettlement;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every condition the demand reading took up is one the account answers for, whatever ended the
 * search first.
 *
 * <p><b>The two halves of the reconciliation have to be over the same conditions.</b> What the
 * answer side answered for is what the way stated, and the reading over the input drops its own
 * word about every one of those on the strength of it. So an account that holds what a walk reached
 * before it stopped leaves conditions named by neither side: the reading gave them up because the
 * answer side had them, and the answer side never got as far as them.
 *
 * <p>Which is what makes an account taken as a difference rather than gathered as a walk goes. A
 * search ends at the first asking nothing composed for, at the first dependency nothing stands in,
 * and at whatever is added beside those — and each of them is a place a gathered list has to
 * remember to fill.
 */
class EveryConditionTheAnswerSideTookUpIsAccountedForTest {

    private static final String TYPES = """
            module example.scope

            data K = { id: Int }
            data R = { k: K, j: K, v: Int }
            data Yes
            data No
            data Answer = Yes | No
            """;

    /**
     * Two calls of one dependency, where the first asks something no value can be composed for.
     *
     * <p>The first asking ends the search for this dependency: nothing composes a value of a
     * comparison between two records, so the row leans on the table the module states. The second
     * asking is never composed for, and what it asks is as much a thing that row does not meet.
     */
    private static final String TWO_CALLS_ONE_OF_WHICH_COMPOSES_NOTHING = TYPES + """

            behavior look : (at: Int) -> R

            behavior decides : (m: Int, n: Int) -> Answer
                depends on look
            let decides (m, n, look) =
                if look(m).k == look(m).j then
                    (if look(n).v > 0 then Yes else No)
                else No

            let same = R { k = K { id = 1 }, j = K { id = 1 }, v = 1 }

            fake look
                | _ -> same
            """;

    /**
     * Two dependencies, where nothing stands the first one in.
     *
     * <p>No table is stated for either, so the first ends the whole standing-in and the second is
     * not asked about at all. What the way asks of the second is a condition the demand reading
     * took up like any other.
     */
    private static final String ONE_DEPENDENCY_NOTHING_STANDS_IN = TYPES + """

            behavior first : (at: Int) -> R
            behavior second : (at: Int) -> R

            behavior decides : (m: Int) -> Answer
                depends on first
                depends on second
            let decides (m, first, second) =
                if first(m).k == first(m).j then
                    (if second(m).v > 0 then Yes else No)
                else No
            """;

    /**
     * A dependency whose demand a value was composed for, beside one nothing stands in.
     *
     * <p>The first composes: a comparison over a number of what it answers is a demand a value is
     * built to meet. The second does not, and no table is stated for it, so the standing-in comes
     * to nothing and no row of this is offered. What was composed was still composed, and a demand
     * a value met is not one nothing composed a value of.
     */
    private static final String ONE_COMPOSES_AND_THE_NEXT_STANDS_IN_WITH_NOTHING = TYPES + """

            behavior first : (at: Int) -> R
            behavior second : (at: Int) -> R

            behavior decides : (m: Int) -> Answer
                depends on first
                depends on second
            let decides (m, first, second) =
                if first(m).v > 0 then
                    (if second(m).k == second(m).j then Yes else No)
                else No
            """;

    /**
     * A demand a value was composed for is not said to be one nothing composed a value of, though
     * the standing-in came to nothing after it.
     *
     * <p>The other direction of the same scope. What a walk reached must not be what the account
     * is taken over — and what it reached and composed must not be forgotten either, or the word
     * for a demand nothing met is put on one a value meets.
     */
    @Test
    void aDemandAValueWasComposedForIsNotSaidToBeOneNothingComposedFor() {
        Set<ConditionReportAnchor> accounted =
                anchorsAccountedFor(ONE_COMPOSES_AND_THE_NEXT_STANDS_IN_WITH_NOTHING);

        assertEquals(1, accounted.size(),
                () -> "the condition of the dependency nothing stands in is answered for, and the"
                        + " one a value was composed for is not among them: " + accounted);
    }

    /** What the second call asks is in the account, though nothing was composed for it. */
    @Test
    void anAskingThatWasNeverComposedForIsStillAccountedFor() {
        assertEquals(2, anchorsAccountedFor(TWO_CALLS_ONE_OF_WHICH_COMPOSES_NOTHING).size(),
                () -> "both conditions of the way are answered for: "
                        + anchorsAccountedFor(TWO_CALLS_ONE_OF_WHICH_COMPOSES_NOTHING));
    }

    /** And so is what the way asks of a dependency the search never reached. */
    @Test
    void aDependencyTheSearchNeverReachedIsStillAccountedFor() {
        assertEquals(2, anchorsAccountedFor(ONE_DEPENDENCY_NOTHING_STANDS_IN).size(),
                () -> "both conditions of the way are answered for: "
                        + anchorsAccountedFor(ONE_DEPENDENCY_NOTHING_STANDS_IN));
    }

    /**
     * Where the conditions of the way are answered for, over every rule of the body.
     *
     * <p>Taken over the rules together because which of them a walk reaches first is not what is
     * under test: a condition named under any rule of the body is one this compiler said something
     * about, and one named under none is the loss this is written for.
     */
    private static Set<ConditionReportAnchor> anchorsAccountedFor(String model) {
        Set<ConditionReportAnchor> out = new LinkedHashSet<>();
        for (RuleSettlement each : settlementsOf(model)) {
            for (DemandGap gap : each.account().onAnAnswer()) {
                out.add(gap.anchor());
            }
        }
        return out;
    }

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
        assertTrue(out.stream().anyMatch(each -> !each.account().onAnAnswer().isEmpty()),
                () -> "and a rule of it was composed for without meeting what the way asks: " + out);
        return out;
    }
}
