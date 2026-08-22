package souther.compiler.query;

import souther.compiler.check.BehaviorContract;
import souther.compiler.check.BehaviorRequirement;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.ast.Hir;
import souther.compiler.examples.Answering;
import souther.compiler.examples.ExampleVerifier;
import souther.compiler.generated.EvaluationArtifact;
import souther.compiler.check.Symbols;

import java.util.List;
import java.util.Map;

/**
 * What a run of a module's rows is made of, assembled once for a caller that runs them itself.
 *
 * <p>{@link Output.Examples} assembles the same state to run a module's rows in bulk, and this is
 * here because the two runs differ in who owns the loop and in nothing else: a row's fixtures are
 * decoded through their derived decoders against this module's symbols and this compile's classes
 * whichever of them asks for it. What is not shared is what a bulk run adds — which source the rows
 * were written in, what a coverage mode asked the emitter for, and how an absent answer travels —
 * none of which a caller running one row at a time has a question about.
 *
 * <p>Reached from outside the compiler, so what it hands back is the thing rows are run against and
 * not a report. Whether a row that failed fails a build is not knowledge of the model.
 */
public final class ExampleRuns {

    private ExampleRuns() {
    }

    /**
     * The module's rows, ready to be run one at a time against what {@code answering} gives.
     *
     * <p>Every argument comes from the compilation and none is a caller's to choose. What an
     * implementation is held to is the module as this reading of the source has it, which is the
     * whole reason the source is read at the time the run happens.
     */
    public static ExampleVerifier evaluating(Db db, String module, Answering answering) {
        Answer<Prepared> prepared = db.ask(new Shapes.Prepared(module));
        Answer<Symbols> scope = Names.derivedSymbols(db, module);
        Answer<Map<String, Sig>> sigs = db.ask(new Bodies.Signatures(module));
        if (!prepared.present() || !scope.present() || !sigs.present()) {
            throw new IllegalStateException("`" + module + "` did not check, so it has no rows to"
                    + " run");
        }
        EvaluationArtifact artifact = db
                .ask(new Output.EvaluationLinked(module, Output.CoverageMode.NONE)).value();
        if (artifact == null) {
            throw new IllegalStateException("`" + module + "` emitted nothing to run its rows"
                    + " against");
        }
        Map<String, List<BehaviorRequirement>> requirements =
                db.ask(new Bodies.Requirements(module)).value();
        Map<String, Hir.FnDef> values = db.ask(new Bodies.ModuleDefinitions(module)).value();
        Map<String, BehaviorContract> contracts = db.ask(new Bodies.Contracts(module)).value();
        return ExampleVerifier.evaluating(
                prepared.value().forExamples(),
                scope.value(),
                sigs.value(),
                artifact,
                () -> Output.declarationsRead(db),
                requirements == null ? Map.of() : requirements,
                Output.evaluationLoader(db),
                values == null ? Map.of() : values,
                Output.deadlineOf(db),
                Output.policyOf(db),
                answering,
                contracts == null ? Map.of() : contracts);
    }
}
