package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.observe.ArmObservation;
import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.source.SourceId;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A row whose evaluation is short of the room the platform supplies for an answer is undecided and
 * not failed (spec §example-evaluation-has-room): the answer is a decimal the language defines, a
 * platform with more room writes it, and nothing about the model was found out. A decimal rounded
 * to a scale of two billion places is one, written with that many digits.
 */
class AnExampleShortOfRoomIsUndecidedAndNotFailedTest {

    private static final String MODEL = """
            module example.room
            data Out = Decimal
            behavior run : (n: Int) -> Out constructs Out
            let run (n) = Out(Decimal.round(n, HALF_UP, 1m))
            example run
              | "far out": (2147483647) -> Out(1m)
            """;

    @Test
    void theRowIsUndecidedAtTheShortage() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        ACompiledModel.refusedWith(List.of("E1941"), compilation);
        SourceId sourceId = compilation.exampleSourcesOf("example.room").getFirst();
        List<RowOutcome> rows = compilation.db()
                .ask(new Output.Examples("example.room", sourceId, ArmObservation.OMIT))
                .value().rows();

        assertEquals(1, rows.size(), rows.toString());
        assertEquals(FailurePhase.OUT_OF_ROOM, rows.getFirst().failurePhase());
        assertFalse(rows.getFirst().failurePhase().failsARow());
    }

    /** And so is a row whose own written value is short of room: the value exists, and it is no
     *  value the row failed to produce. */
    @Test
    void aValueTheRowWritesShortOfRoomIsAShortageToo() {
        CompileException raised = assertThrows(CompileException.class, () -> Compiler.compile("""
                module example.room
                data Out = Decimal
                behavior echo : (d: Decimal) -> Out constructs Out
                let echo (d) = Out(d)
                example echo
                  | "written far out": (Decimal.round(2147483647, HALF_UP, 1m)) -> Out(1m)
                """));

        assertEquals("E1941", raised.code());
    }

    @Test
    void itIsSaidAsAShortageAndNotAsAWrongAnswer() {
        CompileException raised = assertThrows(CompileException.class,
                () -> Compiler.compile(MODEL));

        assertEquals("E1941", raised.code());
    }
}
