package souther.compiler.query;

import souther.compiler.execute.jvm.JvmProgramImages;

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
        Map<String, byte[]> classes = db.ask(new Output.Linked(module)).value();
        return classes == null ? null : Output.loader(db, classes);
    }
}
