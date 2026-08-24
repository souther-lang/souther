package souther.compiler.examples;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.observe.RowIdentity;

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

    private final String module;
    private final Prepared.ExampleExecution rows;
    private final ExampleVerifier verifier;

    /** The behaviors the bound instance implements, worked out once from the instance. */
    private final List<String> bound;

    BoundExamples(String module, Prepared.ExampleExecution rows, ExampleVerifier verifier,
                  List<String> bound) {
        this.module = module;
        this.rows = rows;
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
        for (Prepared.Rows block : rows.examples()) {
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
     *
     * <p>What comes back is the observation and what was said about it. The observation is what a
     * machine decides from; the diagnostics are how a consumer tells a person which value differed
     * and where, which the outcome alone does not carry.
     */
    public RowEvaluation evaluate(RecordedRow row) {
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
                return new RowKey(this, behavior, named);
            }
        }
        throw new IllegalArgumentException("no row of `" + behavior + "` is named `" + name + "`");
    }

    /** Which module's rows these are — the one declaring what the bound instance implements. */
    public String moduleName() {
        return module;
    }

    /** Which behaviors the bound instance answers for. */
    public List<String> boundBehaviors() {
        return bound;
    }

    /**
     * The explicit entries of the tables faking the bound behaviors.
     *
     * <p>Each is an input and an answer in the same form a recorded row is, written for some other
     * behavior's sake and held to nothing until now. Nothing new is written to run them.
     */
    public List<StandinEntry> standinEntries() {
        List<StandinEntry> found = new ArrayList<>();
        for (String behavior : bound) {
            found.addAll(verifier.standinEntries(this, behavior));
        }
        return found;
    }

    /**
     * What the bound implementation answered for {@code row}'s inputs, held to what the behavior
     * declares of what it answers — and to nothing the row records.
     *
     * <p>A different oracle from {@link #evaluate}'s, which holds an answer to the declaration and
     * to the value somebody wrote out. Where the recorded answer is no longer the answer — a world
     * the rows were not recorded in — what the behavior states still is, and this is the face that
     * asks only that.
     *
     * <p>Applied once per call, as {@code evaluate} is and for the same reason: what the
     * implementation answers comes out of world state the caller arranges between calls, and two
     * answers under two worlds are two observations rather than a contradiction.
     *
     * <p>Once the binding has been established, a behavior that states nothing is answered
     * {@link ContractObservation.NothingStated} without the implementation being applied. A binding
     * nothing may be handed to is answered for first: an implementation of another build states
     * nothing that can run, and calling that "the model states nothing" would send its author to
     * write a clause that still would not. To leave a behavior that states nothing out rather than
     * be told about each of its rows, read {@link #behaviorsWithContracts()}.
     */
    public ContractObservation checkContract(RecordedRow row) {
        if (row == null || row.enumeratedBy() != this) {
            throw new IllegalArgumentException("a row belongs to the enumeration that made it");
        }
        return verifier.contractOnly(row.behavior(), row.written());
    }

    /**
     * Which of the bound behaviors have a contract — an {@code ensures} saying something of what
     * they answer.
     *
     * <p>What a behavior declares, asked without applying anything — a behavior writing no
     * {@code ensures} is not among the module's contracts at all, so this reads a declaration rather
     * than predicting a run. For a suite that means to hold only the behaviors with a contract to
     * one, and that would otherwise have to write their names down beside the model.
     *
     * <p>Beside {@link ContractObservation.NothingStated} and not instead of it. A suite over every
     * row is the ordinary way to write one — the arm is what tells an author who did not mean to
     * leave a behavior out — and narrowing by this is the deliberate exception.
     *
     * <p>Walks what is bound on each call and answers a fresh list, so a loop that narrows by it
     * reads it once rather than once per row.
     */
    public List<String> behaviorsWithContracts() {
        List<String> stating = new ArrayList<>();
        for (String behavior : bound) {
            if (verifier.states(behavior)) {
                stating.add(behavior);
            }
        }
        return List.copyOf(stating);
    }

    /**
     * What the implementation answered for {@code entry}'s input, held to what the entry states.
     *
     * <p>Enumerated and observed one at a time, as rows are and for the same reason: what the
     * implementation answers comes out of world state the caller arranges between calls. The same
     * entry may be observed under as many worlds as they like and nothing is retained between calls —
     * two different answers are two observations, not a contradiction.
     */
    public StandinObservation observe(StandinEntry entry) {
        if (entry == null || entry.enumeratedBy() != this) {
            throw new IllegalArgumentException("an entry belongs to the enumeration that made it");
        }
        return verifier.observe(entry.behavior(), entry);
    }
}
