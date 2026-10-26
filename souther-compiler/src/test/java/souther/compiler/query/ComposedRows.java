package souther.compiler.query;

import souther.compiler.check.Sig;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;
import souther.compiler.partition.RowToRun;

import java.util.List;

/**
 * A composed row run against a compilation, the way the generator runs one: through the module's
 * own classes and decoders, so what comes back is what the program answers for the row.
 *
 * <p>For a test that checks a composed row answers what its values work out to, without writing
 * the row back into the source and compiling the module again to run it as an example.
 */
public final class ComposedRows {

    private ComposedRows() {}

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
