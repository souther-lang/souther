package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;
import souther.compiler.check.InvariantChecker.Said;
import souther.compiler.check.InvariantChecker.Verdict;
import souther.compiler.diag.CompileException;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * An order a condition only proves is used where the condition holds, and nowhere else.
 *
 * <p>{@code Date.daysBetween(from, to) > 1} proves {@code to > from}, and is not where that holds:
 * a day apart, the order holds and the condition does not. So the order is known on the side the
 * condition holds on; it is nothing on the side it fails on, where the dates can still stand that
 * way round; and it is not what a clause owing the condition owes, since establishing it leaves the
 * dates a day apart.
 */
class AnOrderACountOnlyProvesIsUsedOnlyWhereItHoldsTest {

    private static final String PERIOD = """
            module demo

            data Period = { from: Date, to: Date }
                invariant %s

            data Backwards

            behavior span : (from: Date, to: Date) -> Period | Backwards
                constructs Period

            let span (from, to) = {
                %s
            }
            """;

    private static final String WHERE_IT_HOLDS = """
            guard Date.daysBetween(from, to) > 1 else Backwards
                Period { from = from, to = to }""";

    private static final String WHERE_IT_FAILS = """
            if Date.daysBetween(from, to) > 1 then Backwards
                else Period { from = from, to = to }""";

    @Test
    void whereTheCountHoldsTheOrderItProvesIsKnown() {
        assertEquals(List.of(Verdict.PROVED),
                verdicts(PERIOD.formatted("to > from", WHERE_IT_HOLDS)));
    }

    /** One day apart fails the count with {@code to} still the later, so neither order is known. */
    @Test
    void whereTheCountFailsNoOrderIsKnown() {
        assertEquals(List.of(Verdict.UNKNOWN),
                verdicts(PERIOD.formatted("from >= to", WHERE_IT_FAILS)));
        assertEquals(List.of(Verdict.UNKNOWN),
                verdicts(PERIOD.formatted("to > from", WHERE_IT_FAILS)));
    }

    /** A clause owing the count is not discharged by the order it proves. */
    @Test
    void theOrderACountProvesDoesNotDischargeTheCount() {
        assertEquals(List.of(Verdict.UNKNOWN), verdicts(PERIOD.formatted(
                "Date.daysBetween(from, to) > 1", """
                        guard to > from else Backwards
                            Period { from = from, to = to }""")));
    }

    /** Where the count is the order, both are known either way round. */
    @Test
    void whereTheCountIsTheOrderItIsKnownOnBothSides() {
        String exact = """
                if Date.daysBetween(from, to) > 0 then Backwards
                    else Period { from = from, to = to }""";
        assertEquals(List.of(Verdict.PROVED), verdicts(PERIOD.formatted("from >= to", exact)));
        assertEquals(List.of(Verdict.PROVED), verdicts(PERIOD.formatted(
                "Date.daysBetween(from, to) > 0", """
                        guard to > from else Backwards
                            Period { from = from, to = to }""")));
    }

    private static List<Verdict> verdicts(String source) {
        List<Said> said = Collections.synchronizedList(new ArrayList<>());
        InvariantChecker.WATCHING = said;
        try {
            Compiler.compileWithWarnings(source);
        } catch (CompileException refused) {
            // A construction the guards refute is an error, and the verdict that says so was
            // reached before it was raised. What is asked here is which verdict.
        } finally {
            InvariantChecker.WATCHING = null;
        }
        List<Verdict> on = said.stream().filter(s -> s.type().equals("Period"))
                .map(Said::verdict).toList();
        assertFalse(on.isEmpty(), "a construction of Period was checked");
        return on;
    }
}
