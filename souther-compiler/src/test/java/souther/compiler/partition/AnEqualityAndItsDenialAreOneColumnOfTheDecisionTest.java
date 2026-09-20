package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * An equality on an order and its denial are one column of the decision, answered two ways.
 *
 * <p>What keeps a decision table exclusive. A body that turns on {@code voucher == "spring"} draws
 * one distinction, and a path that failed it did not draw a second one — read as two columns, there
 * is an assignment where the equality holds and the denial holds with it, which is a combination no
 * row sits in and nothing can show impossible.
 *
 * <p><b>Held here because the shapes the two arrive in differ.</b> A bound on an order and a hole
 * in one are two constraints, on purpose: a run's ends are what a chooser looks between and a hole
 * is a value taken out of it. Each carries the relation the path met, so the column has to be
 * canonicalised from it — and the obvious way to build one, naming the relation the constraint
 * holds, compiles and leaves the table with a column apiece.
 */
class AnEqualityAndItsDenialAreOneColumnOfTheDecisionTest {

    private static final String MODEL = """
            module example.column

            data Yes = { v: Int }
            data No = { why: Int }

            behavior redeem : (voucher: String) -> Yes | No
                constructs Yes
                constructs No

            let redeem (voucher) = {
                guard voucher == "spring" else No { why = 0 }
                Yes { v = 1 }
            }
            """;

    /**
     * One column, whichever way the path met it, and the equality is the one it is written as.
     *
     * <p>The canonical relation of the pair and not the one the arm happens to hold. Which of the
     * two a path took is the outcome beside the column, which is the other half of this.
     */
    @Test
    void theEqualityAndItsDenialAreOneColumn() {
        Set<DecisionCondition> columns = columns();

        assertEquals(1, columns.size(), () -> "one distinction is one column: " + columns);
        DecisionCondition.AnOrderedComparison only = assertInstanceOf(
                DecisionCondition.AnOrderedComparison.class, columns.iterator().next());
        assertEquals(Rel.EQ, only.proposition(),
                "written as the canonical relation of the pair");
        assertEquals("spring", only.at().spelled());
    }

    /** And the two ways the path met it are the two outcomes at that one column. */
    @Test
    void theTwoWaysThePathMetItAreTheOutcomes() {
        assertEquals(Set.of(true, false), outcomes(),
                "the arm that holds the equality and the arm that fails it answer one column");
    }

    /** Every column the rules of this body consulted. */
    private static Set<DecisionCondition> columns() {
        return rules().stream().flatMap(rule -> rule.consulted().keySet().stream())
                .collect(java.util.stream.Collectors.toCollection(java.util.LinkedHashSet::new));
    }

    /** What the rules came out as at the column, which is one entry per way through the body. */
    private static Set<Boolean> outcomes() {
        Set<Boolean> out = new java.util.LinkedHashSet<>();
        for (DecisionRule rule : rules()) {
            for (Map.Entry<DecisionCondition, DecidedCondition> each
                    : rule.consulted().entrySet()) {
                out.add(assertInstanceOf(DecidedCondition.Compared.class, each.getValue(),
                        "a comparison on an order comes out held or denied").held());
            }
        }
        return out;
    }

    private static List<DecisionRule> rules() {
        return DecisionReadings.readToTheEnd(MODEL, "redeem");
    }
}
