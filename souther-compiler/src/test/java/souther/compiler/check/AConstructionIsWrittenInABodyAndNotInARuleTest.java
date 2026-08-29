package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A construction is written in a body and is refused in a rule, which is why the two readings of a
 * written value are not the same reading.
 *
 * <p>{@link Carrier#literalOf(souther.compiler.core.Core, Symbols)} takes the names off what it
 * reads, because a body may compare a position against its own construction:
 * {@code guard at < Cutoff(Time("16:00:00"))}. {@link Carrier#literalOf(souther.compiler.ast.Hir.Expr)}
 * does not, and the difference is not one of the two forgetting. An invariant and an {@code ensures}
 * may not construct a data at all, so the form never reaches the reader that reads them — and
 * peeling there would be a rule about expressions this compiler refuses to have, kept right by
 * nothing.
 *
 * <p>Which makes those two refusals load-bearing for a reader that does not mention them. Written
 * down here, so that admitting a construction into a rule is a failure here rather than a bound
 * that goes missing wherever the reading of it stopped at the name.
 */
class AConstructionIsWrittenInABodyAndNotInARuleTest {

    private static final String TYPES = """
            module demo

            data Ok
            data No
            data Verdict = Ok | No

            data Cutoff = Time
            """;

    private static List<Diagnostic> refused(String model) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(model),
                "a rule constructing a data is refused where it is written");
        return e.diagnostics();
    }

    /** A body may compare a position against its own construction, which is the form `Core` reads. */
    @Test
    void aBodyMayCompareAPositionAgainstItsOwnConstruction() {
        org.junit.jupiter.api.Assertions.assertDoesNotThrow(() -> Compiler.compile(TYPES + """

                behavior pick : (at: Cutoff) -> Verdict
                    constructs Cutoff

                let pick (at) = {
                    guard at < Cutoff(Time("16:00:00")) else No
                    Ok }
                """));
    }

    /** A newtype's own invariant may not, so no bound of one is a construction. */
    @Test
    void anInvariantMayNotConstructOne() {
        assertTrue(refused(TYPES + """

                data Start = Cutoff
                    invariant notBefore = value >= Cutoff(Time("09:00:00"))
                """).stream().anyMatch(d -> d.code().equals("E1105")),
                "an invariant observes the value being built and does not build another");
    }

    /** Nor may a record's, which is where a field's range comes from. */
    @Test
    void aRecordsInvariantMayNotConstructOne() {
        assertTrue(refused(TYPES + """

                data Window = { at: Cutoff }
                    invariant beforeClose = at < Cutoff(Time("16:00:00"))
                """).stream().anyMatch(d -> d.code().equals("E1105")),
                "a field's range is its record's invariant read at the field");
    }

    /** Nor may an `ensures`, whose comparisons draw lines of their own. */
    @Test
    void anEnsuresMayNotConstructOne() {
        assertEquals("E1017", refused(TYPES + """

                behavior at : (t: Cutoff) -> Verdict
                    ensures asked = Ok -> t < Cutoff(Time("16:00:00"))

                let at (t) = Ok
                """).get(0).code(),
                "a clause states a relation and does not build a value to state it against");
    }
}
