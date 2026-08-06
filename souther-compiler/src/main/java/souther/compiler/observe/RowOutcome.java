package souther.compiler.observe;

import souther.compiler.diag.SourceRef;
import souther.compiler.types.TypeName;

import java.util.List;
import java.util.Set;

/**
 * What one {@code example} row turned out to be — the observation every adequacy measure reads.
 *
 * <p>A row is evidence of several different things at once, and which thing depends on how far it got.
 * A row whose expectation was built states that its case is expected; a row that ran states which case
 * the behavior actually produced, whether or not that is the one it expected; only a row that held
 * states that the behavior produces the case the model says it should. So {@link #expectedArm} and
 * {@link #resultArm} are both kept: a row that expected {@code Approved} and saw {@code Rejected} is
 * not evidence for {@code Approved}, but it is evidence that {@code Rejected} can happen.
 *
 * <p>{@link #at} carries a source id as well as a position, because rows are gathered under the module
 * they belong to and a module's rows are written across its own source and any number of attached
 * {@code examples for} files.
 *
 * <p>The combinations that arise, so that a reader knows which are real and a writer knows where a new
 * stop-point belongs:
 *
 * <pre>
 * how it ended               stage               disposition   failurePhase
 * ------------------------------------------------------------------------------
 * recorded, not evaluated    FIXTURES_VALIDATED  PENDING       NONE
 * a wrong arity              NONE                FAILED        INPUT_FIXTURE
 * an input fixture failed    NONE                FAILED        INPUT_FIXTURE
 * the expectation failed     NONE                FAILED        EXPECTED_FIXTURE
 * the expected arm is wrong  NONE                FAILED        EXPECTED_FIXTURE
 * a dependency had no fake   FIXTURES_VALIDATED  FAILED        FAKE_RESOLUTION
 * a fake had no answer       INVOKED             FAILED        FAKE_RESOLUTION
 * an `unreachable` reached   INVOKED             FAILED        INVOCATION
 * an invariant aborted       INVOKED             FAILED        INVOCATION
 * the answer disagreed       COMPARED            FAILED        COMPARISON
 * it held                    COMPARED            HELD          NONE
 * a fixture's helper hung    NONE                INCOMPLETE    TIMEOUT
 * the behavior hung          INVOKED             INCOMPLETE    TIMEOUT
 * no runtime to run against  (as reached)        INCOMPLETE    INFRASTRUCTURE
 * </pre>
 *
 * @param at             where the row is written
 * @param target         the behavior the row is about
 * @param description    the row's business-case name, or null
 * @param stage          how far it got
 * @param disposition    how it ended
 * @param failurePhase   where it stopped, when it did
 * @param expectedArm    the case the row's expectation constructs, or null when the text does not say
 * @param resultArm      the case the behavior answered with, or null when it did not run or did not
 *                       answer with a case
 * @param inputCases     the case each input fixture constructs, in order; an entry is null where the
 *                       text does not say
 * @param inputs         each input as the compiler owns it, in order
 * @param hits           the branch sites this row passed through; empty until branches are measured
 * @param stepsSpent     how many counted points the evaluation passed. What the row cost, in the unit
 *                       it is actually held to — so a build can see how much of the budget its rows
 *                       use before one of them reaches it, which is the only way to set the budget
 *                       from evidence rather than by guessing. Zero for a row that did not run.
 */
public record RowOutcome(SourceRef at,
                         String target,
                         String description,
                         Stage stage,
                         Disposition disposition,
                         FailurePhase failurePhase,
                         TypeName expectedArm,
                         TypeName resultArm,
                         List<TypeName> inputCases,
                         List<ObservedValue> inputs,
                         Set<Integer> hits,
                         long stepsSpent) {

    public RowOutcome {
        // A list that keeps a null in it cannot be List.copyOf'd, and an input whose case the text does
        // not say is exactly that — so the unmodifiable wrapper is taken rather than the copying factory.
        inputCases = inputCases == null ? List.of()
                : java.util.Collections.unmodifiableList(new java.util.ArrayList<>(inputCases));
        inputs = inputs == null ? List.of() : List.copyOf(inputs);
        hits = hits == null ? Set.of() : Set.copyOf(hits);
    }

    /** Whether this row is evidence that the behavior can answer with {@link #resultArm}. A row that
     * disagreed still saw what it saw. */
    public boolean observed() {
        return stage.reached(Stage.INVOKED) && resultArm != null;
    }
}
