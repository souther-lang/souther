package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.Run;
import souther.compiler.observe.Stage;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An outcome records what applied the behavior for that row, and what that application is measured
 * in. Today there is one answerer — the bytecode this compile generated, applied through the loader
 * the run builds — so the answer is the same for every row a compile ran, and this holds it to that
 * while it is still true. What makes the field worth having before a second answerer exists is that
 * it is checkable now: when one arrives, the rows that name it are the ones that changed.
 *
 * <p>The numbers go with the answerer rather than beside it. How many counted points an application
 * passed is a question about code the emitter counted into, so a reader holding
 * {@link Run.Generated} has both the count and what it counts, and a reader of a row that applied
 * nothing has no numbers to read as zero.
 *
 * <p>Which of the two a row is comes from the stage it reached, and the outcome refuses to be built
 * saying otherwise: the two are written from one evaluation and read apart, so a row that says it
 * applied the behavior and says nothing applied it is a state no reader should have to resolve.
 */
class ARowSaysWhatAppliedTheBehaviorTest {

    private static final String MODEL = """
            module example.trip

            data Amount = Int
                invariant value >= 0

            data Draft = { cost: Amount }
            data Submitted = { cost: Amount }
            data Rejected = { reason: String }

            behavior submit : (request: Draft) -> Submitted | Rejected
                constructs Submitted, Rejected

            let submit (request) = {
                guard request.cost.value <= 100 else Rejected { reason = "over" }
                Submitted { cost = request.cost }
            }

            // Nothing runs this one, so its rows are recorded and not applied.
            behavior settle : (request: Draft) -> Submitted
                constructs Submitted
            """;

    /** Rows that ran, rows that failed on the way, and rows nothing can run. */
    private static final String ROWS = MODEL + """

            example submit
                | "under the ceiling" : (Draft { cost = Amount(50) }) -> Submitted
                | "over it" : (Draft { cost = Amount(200) }) -> Rejected
                | "the answer disagrees" : (Draft { cost = Amount(50) }) -> Rejected

            example settle
                | "waiting for a body" : (Draft { cost = Amount(50) }) -> Submitted
            """;

    private static List<RowOutcome> rowsOf(String source) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        List<RowOutcome> rows = new ArrayList<>();
        for (String module : compilation.modules()) {
            for (String id : compilation.exampleSourcesOf(module)) {
                Output.Examples.Of ran =
                        compilation.db().ask(Output.Examples.asked(compilation.db(), module, id)).value();
                if (ran != null) {
                    rows.addAll(ran.rows());
                }
            }
        }
        return rows;
    }

    @Test
    void everyRowThisCompileAppliedNamesTheClassesThisCompileGenerated() {
        List<RowOutcome> rows = rowsOf(ROWS);
        List<RowOutcome> applied = rows.stream().filter(row -> row.stage().reached(Stage.INVOKED)).toList();

        assertEquals(4, rows.size(), "three rows of a behavior with a body and one without");
        assertEquals(3, applied.size(), "the three with a body to run are the ones applied: " + rows);
        for (RowOutcome row : applied) {
            assertInstanceOf(Run.Generated.class, row.run(),
                    "nothing else applies a behavior in a compile: " + row.identity().shown());
        }
    }

    @Test
    void aRowNothingAppliedSaysNothingApplied() {
        RowOutcome waiting = rowsOf(ROWS).stream()
                .filter(row -> row.disposition() == Disposition.PENDING)
                .findFirst().orElseThrow(() -> new AssertionError("the model has a row waiting"));

        assertEquals(new Run.NotRun(), waiting.run(),
                "a row recorded against a behavior with nothing to run it applied nothing");
        assertEquals(Stage.FIXTURES_VALIDATED, waiting.stage(),
                "and it says how far it did get, which is a different question");
    }

    /**
     * What a row cost is inside what ran it. A reader that wants the count takes the arm that defines
     * it, so "passed no counted point" and "ran nothing this compile counts" cannot be read off one
     * number.
     */
    @Test
    void whatARowCostIsReadFromWhatRanIt() {
        RowOutcome held = rowsOf(ROWS).stream()
                .filter(row -> row.disposition() == Disposition.HELD)
                .findFirst().orElseThrow(() -> new AssertionError("a row holds in this model"));

        Run.Generated ran = assertInstanceOf(Run.Generated.class, held.run());
        assertTrue(ran.steps() >= 0, "the count is this compile's own reading");
        assertFalse(ran.hits().isEmpty(),
                "and so are the arms it went through, this compile having emitted what counts them");
    }

    @Test
    void anOutcomeCannotSayItAppliedNothingAndReachedApplication() {
        RowOutcome ran = rowsOf(ROWS).stream()
                .filter(row -> row.stage().reached(Stage.INVOKED))
                .findFirst().orElseThrow();

        assertThrows(IllegalArgumentException.class,
                () -> new RowOutcome(ran.at(), ran.target(), ran.identity(), ran.stage(),
                        ran.disposition(), ran.failurePhase(), ran.expectedArm(), ran.resultArm(),
                        ran.inputCases(), ran.inputs(), new Run.NotRun()),
                "a row that applied the behavior says what applied it");
        assertThrows(IllegalArgumentException.class,
                () -> new RowOutcome(ran.at(), ran.target(), ran.identity(), Stage.FIXTURES_VALIDATED,
                        ran.disposition(), ran.failurePhase(), ran.expectedArm(), ran.resultArm(),
                        ran.inputCases(), ran.inputs(), new Run.Generated(1L, Set.of())),
                "and one that did not has nothing to say applied it");
    }
}
