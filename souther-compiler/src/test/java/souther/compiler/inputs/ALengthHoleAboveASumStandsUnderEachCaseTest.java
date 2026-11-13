package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.numeric.OrderedRuns;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * The lengths a clause above a sum takes out from between its ends are taken out under each case,
 * as they are where no sum is in the way: a narrowing does not change what a rule says.
 */
class ALengthHoleAboveASumStandsUnderEachCaseTest {

    private static final String THROUGH_A_SUM = """
            module g

            data Paging = { name: String }
            data A = { ...Paging, x: Int }
            data B = { ...Paging, y: Int }
            data Q = A | B

            data Holder = { q: Q }
                invariant fits = String.length(q.name) <= 10 && String.length(q.name) /= 7

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    @Test
    void theRunsStandAtTheSharedFieldUnderEachCase() {
        InputDomain record = reading(THROUGH_A_SUM.replace("q: Q", "q: A"));
        OrderedRuns underTheRecord = runsAt(record.at(TermPath.of("h").then("q").then("name")));
        assertNotNull(underTheRecord, "the clause takes a length out of the field of a record");

        InputDomain sum = reading(THROUGH_A_SUM);
        for (Case each : sum.at(TermPath.of("h").then("q")).obligationCases()) {
            if (each instanceof Case.SumCase one) {
                Position at = sum.at(TermPath.of("h").then("q").refine(Refinement.of(one))
                        .then("name"));
                assertEquals(underTheRecord, runsAt(at), "under " + one.leaf().name());
            }
        }
    }

    private static OrderedRuns runsAt(Position at) {
        return at.bounds().stream()
                .filter(each -> each.term() instanceof NumericTerm.TakenOf)
                .map(PositionBounds::runsLeft).filter(runs -> runs != null).findFirst()
                .orElse(null);
    }

    private static InputDomain reading(String source) {
        Compilation compilation =
                Compilation.ofSources(List.of(source), souther.compiler.meta.ModulePath.EMPTY);
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        return InputDomain.of(sigs.get("read"), reading,
                TypeCardinality.Counts.workedOutIn(reading),
                souther.compiler.carrier.Membership.none());
    }
}
