package souther.compiler.observe;

import souther.compiler.diag.SourceRef;
import souther.compiler.types.TypeSymbol;

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
 * <p>Whether the behavior was applied is the {@link Stage} column: everything at {@code INVOKED} or
 * past it says what applied it ({@link Run}), and everything before it says nothing did.
 *
 * @param at             where the row is written
 * @param target         the behavior the row is about
 * @param identity       what the row names itself. A {@link RowIdentity.Named} is unique among the
 *                       rows this module writes for {@link #target}, so something outside the file
 *                       can say which row it means; a {@link RowIdentity.Unnamed} can be shown and
 *                       not addressed
 * @param stage          how far it got
 * @param disposition    how it ended
 * @param failurePhase   where it stopped, when it did
 * @param expectedArm    the case the row's expectation constructs, or null when the text does not say
 * @param resultArm      the case the behavior answered with, or null when it did not run or did not
 *                       answer with a case
 * @param inputCases     the case each input fixture constructs, in order; an entry is null where the
 *                       text does not say
 * @param inputs         each input as the compiler owns it, in order
 * @param run            what applied the behavior, and what that application is measured in. A row
 *                       that reached {@link Stage#INVOKED} says what applied it and a row that did
 *                       not says nothing did, which is held to at construction: the two are
 *                       different cuts of one evaluation and cannot be recorded disagreeing. What a
 *                       row cost is inside the arm it is defined for, so a build reading it has the
 *                       answerer in hand — how much of the budget a row spends is a fact about code
 *                       this compile counted into, and there is no such number for code it did not
 *                       write
 */
public record RowOutcome(SourceRef at,
                         String target,
                         RowIdentity identity,
                         Stage stage,
                         Disposition disposition,
                         FailurePhase failurePhase,
                         TypeSymbol expectedArm,
                         TypeSymbol resultArm,
                         List<TypeSymbol> inputCases,
                         List<ObservedValue> inputs,
                         Run run) {

    public RowOutcome {
        // A list that keeps a null in it cannot be List.copyOf'd, and an input whose case the text does
        // not say is exactly that — so the unmodifiable wrapper is taken rather than the copying factory.
        inputCases = inputCases == null ? List.of()
                : java.util.Collections.unmodifiableList(new java.util.ArrayList<>(inputCases));
        inputs = inputs == null ? List.of() : List.copyOf(inputs);
        if (stage.reached(Stage.INVOKED) == run instanceof Run.NotRun) {
            // Held here because the two are written from one evaluation and read apart: a stage that
            // says the behavior was applied and a run that says nothing applied it is a state no
            // evaluation produces, and a reader that met it would have to decide which half to trust.
            throw new IllegalArgumentException(
                    "a row that applied the behavior says what applied it, and one that did not says "
                            + "nothing did: " + stage + " with " + run);
        }
    }

    /** Whether this row is evidence that the behavior can answer with {@link #resultArm}. A row that
     * disagreed still saw what it saw. */
    public boolean observed() {
        return stage.reached(Stage.INVOKED) && resultArm != null;
    }
}
