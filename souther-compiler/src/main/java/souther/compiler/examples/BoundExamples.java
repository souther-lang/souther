package souther.compiler.examples;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.observe.RowIdentity;
import souther.compiler.observe.RowOutcome;

import java.util.ArrayList;
import java.util.List;

/**
 * The rows a binding makes runnable, and the running of one of them.
 *
 * <p>Two questions and no third. An enumeration of what can be run, and the evaluation of one of
 * them: the loop over them is not owned here, and the reason is not test-framework hygiene but what
 * a real environment means. A bound implementation answers out of world state — what is in a table,
 * what a clock says, what a file holds — and that state is the caller's, changed between rows and
 * invisible here. The owner of what changes between iterations owns the loop.
 *
 * <p>So there is no bulk {@code evaluate()}, and none of the hooks one would grow: before, after,
 * around, transaction, retry, parallelism. Those are a test framework, and one exists. The
 * compile-time run keeps evaluating in bulk because there the environment is the fakes and the run
 * owns them.
 *
 * <p>What a {@code FAILED} or {@code INCOMPLETE} row means for a suite is decided by whoever turns
 * outcomes into tests. Nothing is recorded: a row that held says this implementation, in this
 * environment, answered it — which is what a test result is, and persisting it would let an adequacy
 * report say a behavior is verified while reading a number produced by a build that had a database.
 */
public final class BoundExamples {

    private final SoutherExamples of;
    private final ExampleVerifier verifier;

    /** The behaviors the bound instance implements, worked out once from the instance. */
    private final List<String> bound;

    BoundExamples(SoutherExamples of, ExampleVerifier verifier, List<String> bound) {
        this.of = of;
        this.verifier = verifier;
        this.bound = List.copyOf(bound);
    }

    /**
     * The recorded rows this binding makes runnable, in the order they are written.
     *
     * <p>The rows of what was bound, and no others. A behavior with a body of its own was runnable
     * before anything was bound and is run where a compile runs it; what a binding adds is the rows
     * that had nothing to run them.
     */
    public List<RecordedRow> rows() {
        List<RecordedRow> found = new ArrayList<>();
        for (Prepared.Rows block : of.module().examples()) {
            Hir.Example written = block.read();
            if (!bound.contains(written.target())) {
                continue;
            }
            for (Hir.ExampleRow row : written.rows()) {
                found.add(new RecordedRow(this, written.target(), row));
            }
        }
        return found;
    }

    /**
     * What happened when {@code row} ran.
     *
     * <p>Takes the enumerated row and not a {@link RowKey}: a row written without a name still runs,
     * and keyed evaluation would silently drop every unnamed row of the behavior.
     *
     * <p>The same row may be evaluated as often as the caller likes, under as many worlds as they
     * arrange, and nothing of one evaluation is kept for the next. Two different answers under two
     * worlds are two observations and not a contradiction.
     */
    public RowOutcome evaluate(RecordedRow row) {
        if (row == null || row.enumeratedBy() != this) {
            throw new IllegalArgumentException("a row belongs to the enumeration that made it");
        }
        return verifier.one(row.behavior(), row.written());
    }

    /**
     * The address of {@code behavior}'s row written as {@code name}.
     *
     * <p>Resolved here, so a name nothing answers to fails at resolution rather than as setup that
     * silently never runs. What is resolved against is the rows as written, which the compiler holds
     * to carrying one name each within a behavior — so this finds one row or none, never two.
     */
    public RowKey row(String behavior, String name) {
        for (RecordedRow candidate : rows()) {
            if (candidate.behavior().equals(behavior)
                    && candidate.identity() instanceof RowIdentity.Named named
                    && named.name().equals(name)) {
                return new RowKey(behavior, named);
            }
        }
        throw new IllegalArgumentException("no row of `" + behavior + "` is named `" + name + "`");
    }

    /** Which behaviors the bound instance answers for. */
    public List<String> boundBehaviors() {
        return bound;
    }
}
