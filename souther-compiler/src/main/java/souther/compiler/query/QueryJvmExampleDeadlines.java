package souther.compiler.query;

import souther.compiler.examples.Deadline;
import souther.compiler.execute.jvm.JvmExampleDeadlines;

import java.time.Duration;

/**
 * How this compiler answers what the JVM implementation runs a row under.
 *
 * <p>The arrangement beside {@link QueryJvmProgramImages}, for the other thing that implementation
 * needs and the language does not hand it. A deadline is built from the wait the language handed
 * over and the stack this compilation makes a worker with, or said outright by a caller with a
 * reason to; turning those into the arrangement that keeps them is this compiler's side of the seam
 * rather than the implementation's.
 *
 * <p>Asked, not held. A caller says a deadline after the implementation has been named, so one read
 * at construction would be the one it replaced.
 */
final class QueryJvmExampleDeadlines implements JvmExampleDeadlines {

    private final Db db;

    QueryJvmExampleDeadlines(Db db) {
        this.db = db;
    }

    @Override
    public Deadline forThisCompile(Duration outerTimeout) {
        return Output.deadlineOf(db, outerTimeout);
    }
}
