package souther.compiler.query;

import souther.compiler.execute.jvm.JvmProgramImage;
import souther.compiler.execute.jvm.JvmProgramImages;
import souther.compiler.generated.EvaluationArtifact;
import souther.compiler.jvm.ClassFileImage;

import java.util.Map;

/**
 * How this compiler answers what the JVM implementation needs of it.
 *
 * <p>The one place that knows both. {@code ProgramExecution} is asked in the language's words and
 * the implementation behind it is the JVM's, so something has to turn "the classes of this module"
 * into the query that produces them — and if that something were the implementation, a second one
 * would begin by learning this compiler's query graph, which is the dependency this whole boundary
 * exists to turn around.
 *
 * <p>The same arrangement the checked-program boundary has: one adapter reads the compilation, and
 * nothing on the other side of it does.
 */
final class QueryJvmProgramImages implements JvmProgramImages {

    private final Db db;

    QueryJvmProgramImages(Db db) {
        this.db = db;
    }

    @Override
    public ClassLoader compileTimeLoader(String module) {
        Map<String, ClassFileImage> classes = db.ask(new Output.Linked(module)).value();
        return classes == null ? null : Output.loader(db, classes);
    }

    /**
     * The one program, read off what this compilation measures. Recording the arms is the only way
     * the two programs differ, and the recording one may stand wherever the other would: a probe or
     * an arm rewrite does nothing unless a run is recording or rewriting, and measuring never makes
     * a module that compiles into one that does not ({@code Backend.generate} writes a method again
     * without what it could not hold).
     */
    @Override
    public JvmProgramImage evaluating(String module) {
        EvaluationArtifact program =
                db.ask(new Output.EvaluationLinked(module, Adequacy.armsAsked(db))).value();
        if (program == null) {
            return null;
        }
        // Read when something has to be held to a declaration rather than now: a compile's own
        // answers are of the module being evaluated by being of this compile of it, and every
        // answer a run has today is one of those.
        return new JvmProgramImage(program, Output.evaluationLoader(db),
                () -> Output.declarationsRead(db));
    }
}
