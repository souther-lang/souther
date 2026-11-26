package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.execute.RunStop;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;
import souther.compiler.partition.RowToRun;
import souther.compiler.partition.StoodInAnswer;
import souther.compiler.partition.WhereARunStopped;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A row a search runs stands a behavior with a body in with a {@code with} as a written row does,
 * and what it answers is held to what that behavior declares in the same place.
 *
 * <p>So a stand-in answering what the declaration rules out is not an answer the search observes:
 * the run got none, and stopped at the clause of the behavior stood in for — not at one of the
 * behavior the row is for.
 */
class AComposedStandInIsHeldToWhatTheBehaviorDeclaresTest {

    private static final String MODEL = """
            module probe.kept exposing ( top )

            behavior lookup : (key: Int) -> Int

            behavior convert : (a: Int, b: Int) -> Int
                depends on lookup
                ensures bounded = value < a + 100
            let convert (a, b, lookup) = lookup(a) + b

            behavior top : (a: Int, b: Int) -> Int
                depends on convert
            let top (a, b, convert) = convert(a, b)

            example top
                | "past the bound" : (1, 2) with convert = 500 -> 500
            """;

    @Test
    void aStandInTheDeclarationRulesOutStopsTheRunAtItsClause() {
        Compilation compilation = Compilation.ofSources(List.of(MODEL), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.refusedWith(List.of("E1905"), compilation);
        Db db = compilation.db();
        String module = compilation.modules().get(0);
        Sig sig = db.ask(new Bodies.Signatures(module)).value().get("top");

        Generator.ObservedRun ran = Adequacy.runningRowsOf(db, module,
                Adequacy.trialling(db, module), "top", sig,
                RequiredDependencies.of(db, module, "top")).run(written(compilation));

        assertEquals(new AnswerObservation.NotAnswered(), ran.answer());
        assertEquals(Optional.of(
                        new RunStop.AtAnEnsures("probe.kept", "convert", Optional.of("bounded"))),
                ran.stopped().map(WhereARunStopped::stop));
    }

    /** The written row, its {@code with} included, as a composed row is handed to a run. */
    private static RowToRun written(Compilation compilation) {
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        ValueName.Behavior target = new ValueName.Behavior(module, "top");
        Hir.ExampleRow row = prepared.examples().stream()
                .filter(block -> target.equals(block.exampled()))
                .map(Prepared.Example::read)
                .flatMap(block -> block.rows().stream())
                .findFirst().orElseThrow();
        return new RowToRun(row.inputs().stream()
                .map(input -> new FixtureTemplate("past the bound", input)).toList(),
                List.of(new StoodInAnswer.OnTheRow(new ValueName.Behavior(module, "convert"),
                        new FixtureTemplate("past the bound", row.withs().getFirst().value()))));
    }
}
