package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * A name nothing declares, standing in a row that applies an intrinsic, is the naming error
 * resolution already reported.
 *
 * <p>The walk that settles which instance an intrinsic is emitted for reads the row's arguments,
 * and an argument can be a name resolution answered with nothing. What that walk may do with one is
 * fail to settle the call: the mistake was reported where the name is written, and reported once —
 * a second producer repeating it says the same thing twice about one fact.
 *
 * <p>Held against every argument position and against a callee that goes nowhere near that walk,
 * because what decides the answer is neither. A name that denotes nothing is a naming error
 * wherever it is written.
 */
class ARowApplyingAnIntrinsicRefusesANameItCannotAnswerTest {

    private static final String MODULE = """
            module demo

            data Ok = { n: Int }

            behavior take : (d: Decimal) -> Ok
                constructs Ok
            let take (d) = Ok { n = 1 }

            example take
                | "row" : (%s) -> Ok { n = 1 }
            """;

    private static List<String> verdict(String operand) {
        try {
            Compiler.compile(MODULE.formatted(operand));
            return List.of("ok");
        } catch (CompileException e) {
            return e.diagnostics().stream().map(Diagnostic::code).toList();
        }
    }

    /**
     * Every unresolved name a row's call is written over is the one naming error, once.
     *
     * <p>Asked as one map, because what is held is that the answer does not vary with the callee or
     * the position: a case fixing the one that failed is satisfied by a second answer written for
     * the others.
     */
    @Test
    void aNameNothingDeclaresInAnIntrinsicsRowCallIsTheNamingErrorOnce() {
        Map<String, String> operands = new LinkedHashMap<>();
        operands.put("a misspelt mode", "Decimal.round(2, HalfUp, 1.005m)");
        operands.put("an unresolved first argument", "Decimal.round(nope, HALF_UP, 1.005m)");
        operands.put("an unresolved value argument", "Decimal.round(2, HALF_UP, nope)");
        operands.put("a misspelt mode of divide", "Decimal.divide(1.0m, 2.0m, 2, HalfUp)");
        operands.put("a callee that is not an intrinsic", "Int.max(1, nope)");

        Map<String, List<String>> expected = new LinkedHashMap<>();
        operands.forEach((what, _) -> expected.put(what, List.of("E1023")));
        Map<String, List<String>> got = new LinkedHashMap<>();
        operands.forEach((what, operand) -> got.put(what, verdict(operand)));
        assertEquals(expected, got);
    }

    /** The same call, spelled as core declares the mode, is settled and run. */
    @Test
    void theSameCallSpelledAsCoreDeclaresItIsSettled() {
        assertEquals(List.of("ok"), verdict("Decimal.round(2, HALF_UP, 1.005m)"));
    }

    /**
     * And a body writing the same call answers the same, as it did before the row did.
     *
     * <p>What decided the answer was the walk a row's operands go through and nothing about the
     * call, so the body is held here beside the row: a fix that settled the row by teaching that
     * walk to make something up would show as the two coming apart.
     */
    @Test
    void aBodyWritingTheSameCallIsTheSameNamingError() {
        String body = """
                module demo

                data Ok = { n: Int }

                behavior take : (d: Decimal) -> Ok
                    constructs Ok
                let take (d) = Ok { n = 1 }

                let round2 (r: Decimal) : Decimal = Decimal.round(2, HalfUp, r)
                """;
        try {
            Compiler.compile(body);
            fail("`HalfUp` names nothing in a body either");
        } catch (CompileException e) {
            assertEquals(List.of("E1023"),
                    e.diagnostics().stream().map(Diagnostic::code).toList(), e.getMessage());
        }
    }
}
