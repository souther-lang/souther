package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.Stage;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An {@code example} on a behavior that has no {@code let} yet.
 *
 * <p>A model being migrated onto starts injected everywhere, and the rows harvested from the system it
 * replaces are the record of what each behavior owes. Refusing them would mean keeping that record
 * somewhere the compiler cannot read, which is where it stops being checked. So they are recorded:
 * every fixture is built, so a value that breaks an invariant is found the day it is written, and
 * evaluation begins by itself the moment the {@code let} arrives.
 */
class CompileInjectedExamplePendingTest {

    private static final String BASE = """
            module example.member
            import String ( length )

            data MemberId = String
                invariant length(value) > 0

            data Found = { id: MemberId }
            data Missing = { reason: String }
            """;

    private static final String INJECTED = BASE + """
            behavior findMember : (id: MemberId) -> Found | Missing
            """;

    private static CompileException err(String model) {
        return assertThrows(CompileException.class, () -> Compiler.compile(model));
    }

    private static List<RowOutcome> rows(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.answerEverything();
        return compilation.db()
                .ask(new Output.Examples(compilation.modules().get(0), compilation.sourceIds().get(0)))
                .value().rows();
    }

    @Test
    void aRowOnAnInjectedBehaviorCompilesAndIsRecorded() {
        List<RowOutcome> rows = rows(INJECTED + """

                example findMember
                    | "known"   : (MemberId("m-1")) -> Found { id = MemberId("m-1") }
                    | "unknown" : (MemberId("m-9")) -> Missing { reason = "no such member" }
                """);

        assertEquals(2, rows.size());
        for (RowOutcome row : rows) {
            assertEquals(Disposition.PENDING, row.disposition());
            assertEquals(Stage.FIXTURES_VALIDATED, row.stage(),
                    "everything a row can be held to without a body was checked");
            assertEquals(FailurePhase.NONE, row.failurePhase(), "waiting is not failing");
            assertEquals(1, row.inputs().size());
        }
        assertEquals(List.of("Found", "Missing"),
                rows.stream().map(r -> r.expectedArm().name()).toList());
    }

    /** The point of building the fixtures anyway: a value the legacy system produced but the model
     * forbids is found the day the row is written, not the day the `let` is. */
    @Test
    void aPendingRowsInputStillGoesThroughItsInvariant() {
        assertEquals("E1903", err(INJECTED + """

                example findMember
                    | (MemberId("")) -> Missing { reason = "empty" }
                """).diagnostic().code());
    }

    @Test
    void aPendingRowsExpectationStillHasToBeACaseOfTheOutput() {
        assertEquals("E1904", err(INJECTED + """

                example findMember
                    | (MemberId("m-1")) -> MemberId("m-1")
                """).diagnostic().code());
    }

    /**
     * A row's expectation is built by the output type's decoder, not by the behavior, so a target with
     * no {@code constructs} of its own still takes rows that name what it will answer with. An injected
     * behavior never has {@code constructs} — what it builds, it builds in Java.
     */
    @Test
    void aPendingRowNeedsNoConstructionAuthority() {
        assertDoesNotThrow(() -> Compiler.compile(INJECTED + """

                example findMember
                    | (MemberId("m-1")) -> Found { id = MemberId("m-1") }
                """));
    }

    /** The moment that matters in a migration: the rows stop waiting and start judging. */
    @Test
    void writingTheLetStartsEvaluatingTheRowsThatWereWaiting() {
        String implemented = BASE + """
                behavior findMember : (id: MemberId) -> Found | Missing
                    constructs Missing

                let findMember (id) = Missing { reason = "not implemented" }

                example findMember
                    | (MemberId("m-1")) -> Missing { reason = "not implemented" }
                """;

        List<RowOutcome> rows = rows(implemented);
        assertEquals(1, rows.size());
        assertEquals(Disposition.HELD, rows.get(0).disposition());
        assertEquals(Stage.COMPARED, rows.get(0).stage());

        String wrong = implemented.replace("-> Missing { reason = \"not implemented\" }\n",
                "-> Found { id = MemberId(\"m-1\") }\n");
        assertTrue(wrong.contains("-> Found"), "the row under test was rewritten");
        assertEquals("E1905", err(wrong).diagnostic().code(),
                "a row that was merely recorded now has to hold");
    }
}
