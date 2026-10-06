package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.Stage;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;
import souther.compiler.partition.RowToRun;
import souther.compiler.source.SourceId;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A run says what the behavior answered, beside where it went.
 *
 * <p>What is kept is what came back and not what the row states: a row that wrote one answer and got
 * another carries the one it got, and a row whose answer is owed carries it as well. A run that got
 * no answer back — it aborted, or nothing applied it — says it got none, which is a different thing
 * from an answer this compiler could not read.
 *
 * <p>A row somebody wrote and a row the generator composed are run by different callers, and the
 * answer is read the same way for both: the same inputs come back as the same value whichever of them
 * ran it.
 */
class ARunSaysWhatTheBehaviorAnsweredTest {

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

            behavior discount : (request: Draft) -> Submitted
                constructs Submitted

            let discount (request) =
                if request.cost.value > 100
                    then Submitted { cost = request.cost }
                    else unreachable "a request this small never arrives"

            // Nothing runs this one, so its rows are recorded and not applied.
            behavior settle : (request: Draft) -> Submitted
                constructs Submitted

            example submit
                | "the answer disagrees" : (Draft { cost = Amount(50) }) -> Rejected
                | "over it" : (Draft { cost = Amount(200) }) -> <?>

            example discount
                | "below nothing" : (Draft { cost = Amount(50) }) -> Submitted

            example settle
                | "waiting for a body" : (Draft { cost = Amount(50) }) -> Submitted
            """;

    @Test
    void aRowThatAnsweredCarriesWhatCameBackAndNotWhatItStates() {
        RowOutcome row = rowNamed(compiled(), "the answer disagrees");

        ObservedValue.Constructed answer = assertInstanceOf(ObservedValue.Constructed.class,
                assertInstanceOf(AnswerObservation.Answered.class, row.answer()).value(),
                "the row wrote Rejected and the behavior answered a value");
        assertEquals(row.resultArm(), answer.declaredAs(),
                "the answer is of the case the run answered with, not the one the row named");
        assertEquals(new ObservedValue.Integer(50),
                assertInstanceOf(ObservedValue.Constructed.class, answer.field("cost"))
                        .field("value"),
                "and it is the whole value, down to what it holds");
    }

    @Test
    void aRowWhoseAnswerIsOwedCarriesTheAnswerAllTheSame() {
        RowOutcome row = rowNamed(compiled(), "over it");

        assertEquals(Stage.ANSWERED, row.stage());
        assertInstanceOf(AnswerObservation.Answered.class, row.answer(),
                "nothing is held to it, and it came back: " + row.answer());
    }

    @Test
    void aRowThatAbortedGotNoAnswer() {
        RowOutcome row = rowNamed(compiled(), "below nothing");

        assertEquals(Stage.INVOKED, row.stage(),
                "the invariant stopped the body it was applied to: " + row);
        assertEquals(new AnswerObservation.NotAnswered(), row.answer());
    }

    @Test
    void aRowNothingAppliedGotNoAnswer() {
        RowOutcome row = rowNamed(compiled(), "waiting for a body");

        assertEquals(new AnswerObservation.NotAnswered(), row.answer());
    }

    /** The stage and the answer are one evaluation read apart, and cannot be recorded disagreeing. */
    @Test
    void aRowCannotSayItAnsweredWithNothingToShowForIt() {
        RowOutcome row = rowNamed(compiled(), "the answer disagrees");

        assertThrows(IllegalArgumentException.class, () -> new RowOutcome(row.at(), row.target(),
                row.identity(), row.expectation(), row.stage(), row.disposition(),
                row.failurePhase(), row.expectedArm(), row.resultArm(),
                new AnswerObservation.NotAnswered(), row.inputCases(), row.inputs(),
                row.statement(), row.run(), List.of()));
        RowOutcome aborted = rowNamed(compiled(), "below nothing");
        assertThrows(IllegalArgumentException.class, () -> new RowOutcome(aborted.at(),
                aborted.target(), aborted.identity(), aborted.expectation(), aborted.stage(),
                aborted.disposition(), aborted.failurePhase(), aborted.expectedArm(),
                aborted.resultArm(), row.answer(), aborted.inputCases(), aborted.inputs(),
                aborted.statement(), aborted.run(), List.of()));
    }

    @Test
    void aComposedRowAnswersWhatTheWrittenRowDid() {
        Compilation compilation = compiled();
        RowOutcome written = rowNamed(compilation, "the answer disagrees");

        Generator.ObservedRun composed = run(compilation, "submit", "the answer disagrees");

        assertEquals(written.answer(), composed.answer(),
                "the same inputs, run by the generator's caller, come back as the same value");
        assertInstanceOf(Generator.Watched.Ran.class, composed.watched(),
                "and where it went is still recorded beside it");
    }

    @Test
    void aComposedRowThatAbortedWentWhereItWentAndGotNoAnswer() {
        Generator.ObservedRun composed = run(compiled(), "discount", "below nothing");

        assertEquals(new AnswerObservation.NotAnswered(), composed.answer());
        assertInstanceOf(Generator.Watched.Ran.class, composed.watched(),
                "the run was recorded up to where it stopped");
    }

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSources(List.of(MODEL), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static RowOutcome rowNamed(Compilation compilation, String name) {
        List<RowOutcome> rows = new ArrayList<>();
        for (String module : compilation.modules()) {
            for (SourceId id : compilation.exampleSourcesOf(module)) {
                Output.Examples.Of ran = compilation.db()
                        .ask(Output.Examples.asked(compilation.db(), module, id)).value();
                if (ran != null) {
                    rows.addAll(ran.rows());
                }
            }
        }
        return rows.stream().filter(row -> row.identity().shown().equals(name)).findFirst()
                .orElseThrow(() -> new AssertionError("no row `" + name + "` in " + rows));
    }

    /** The written row {@code name} of {@code behavior}, run the way a composed row is. */
    private static Generator.ObservedRun run(Compilation compilation, String behavior,
                                             String name) {
        Db db = compilation.db();
        String module = compilation.modules().get(0);
        Prepared prepared = db.ask(new Shapes.Prepared(module)).value();
        Sig sig = db.ask(new Bodies.Signatures(module)).value().get(behavior);
        assertNotNull(sig, "the behavior has a signature");
        Hir.ExampleRow row = prepared.examples().stream()
                .map(Prepared.Example::read)
                .filter(block -> block.target().equals(behavior))
                .flatMap(block -> block.rows().stream())
                .filter(each -> each.identity().shown().equals(name))
                .findFirst().orElseThrow();
        Generator.Trial trial = Adequacy.runningRowsOf(Adequacy.trialling(db, module), behavior,
                sig, Adequacy.numberingOf(db, module),
                RequiredDependencies.of(db, module, behavior));
        return trial.run(RowToRun.of(row.inputs().stream()
                .map(input -> new FixtureTemplate(name, input)).toList()));
    }
}
