package souther.compiler.query;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.coverage.RunRewrite;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;
import souther.compiler.partition.RowToRun;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A composed row run against a compilation, the way the generator runs one: through the module's
 * own classes and decoders, so what comes back is what the program answers for the row.
 *
 * <p>For a test that checks a composed row answers what its values work out to, without writing
 * the row back into the source and compiling the module again to run it as an example.
 */
public final class ComposedRows {

    private ComposedRows() {}

    /**
     * The rewrites a search for a row is asked under when it chooses the written row {@code name}
     * of {@code behavior}: those of the walks and arms the row's run went through.
     */
    public static List<RunRewrite> rewritesThrough(Compilation compilation, String behavior,
                                                   String name) {
        Db db = compilation.db();
        String module = compilation.modules().getFirst();
        Sig sig = db.ask(new Bodies.Signatures(module)).value().get(behavior);
        Generator.Trial trial = Adequacy.runningRowsOf(db, module, Adequacy.trialling(db, module),
                behavior, sig, RequiredDependencies.of(db, module, behavior));
        Generator.ObservedRun ran = trial.run(rowNamed(compilation, behavior, name));
        return trial.rewritesThrough(
                assertInstanceOf(Generator.Watched.Ran.class, ran.watched()).seen());
    }

    /** What running the written row {@code name} of {@code behavior} was seen to do. */
    public static Generator.Watched watched(Compilation compilation, String behavior,
                                            String name) {
        Db db = compilation.db();
        String module = compilation.modules().getFirst();
        Sig sig = db.ask(new Bodies.Signatures(module)).value().get(behavior);
        Generator.Trial trial = Adequacy.runningRowsOf(db, module, Adequacy.trialling(db, module),
                behavior, sig, RequiredDependencies.of(db, module, behavior));
        return trial.run(rowNamed(compilation, behavior, name)).watched();
    }

    /** The written row {@code name} of {@code behavior}, as a composed row is handed to a run. */
    public static RowToRun rowNamed(Compilation compilation, String behavior, String name) {
        Prepared prepared = compilation.db()
                .ask(new Shapes.Prepared(compilation.modules().getFirst())).value();
        Hir.ExampleRow row = prepared.examples().stream()
                .map(Prepared.Example::read)
                .filter(block -> block.target().equals(behavior))
                .flatMap(block -> block.rows().stream())
                .filter(each -> each.identity().shown().equals(name))
                .findFirst().orElseThrow();
        return RowToRun.of(row.inputs().stream()
                .map(input -> new FixtureTemplate(name, input)).toList());
    }

    /** What {@code behavior} of the compilation's first module answers for {@code row}. */
    public static AnswerObservation answer(Compilation compilation, String behavior,
                                           List<FixtureTemplate> row) {
        Db db = compilation.db();
        String module = compilation.modules().get(0);
        Sig sig = db.ask(new Bodies.Signatures(module)).value().get(behavior);
        if (sig == null) {
            throw new IllegalArgumentException("no behavior `" + behavior + "` in " + module);
        }
        Generator.Trial trial = Adequacy.runningRowsOf(db, module, Adequacy.trialling(db, module),
                behavior, sig, RequiredDependencies.of(db, module, behavior));
        return trial.run(RowToRun.of(row)).answer();
    }
}
