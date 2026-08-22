package souther.compiler.observe;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.TypeSymbol;

import java.util.List;

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
 * the values broke a clause  FIXTURES_VALIDATED  FAILED        ENSURES
 * a dependency had no fake   FIXTURES_VALIDATED  FAILED        FAKE_RESOLUTION
 * a fake had no answer       INVOKED             FAILED        FAKE_RESOLUTION
 * an `unreachable` reached   INVOKED             FAILED        INVOCATION
 * an invariant aborted       INVOKED             FAILED        INVOCATION
 * the answer disagreed       COMPARED            FAILED        COMPARISON
 * it held                    COMPARED            HELD          NONE
 * a fixture's helper hung    NONE                INCOMPLETE    TIMEOUT
 * the behavior hung          INVOKED             INCOMPLETE    TIMEOUT
 * it could not be handed on  FIXTURES_VALIDATED  INCOMPLETE    VALUE_CROSSING
 * the answer was not this
 *   model's to hand it to    FIXTURES_VALIDATED  INCOMPLETE    ANSWERER_ESTABLISHMENT
 * </pre>
 *
 * <p>The last two share a stage and a disposition and are not the same thing, which is what the
 * phase is for. {@link FailurePhase#VALUE_CROSSING} is a row that could not be handed on: the value
 * it built could not be put in the form an answerer of other classes reads, and whether the answer
 * is of this model was never in question. {@link FailurePhase#ANSWERER_ESTABLISHMENT} is that
 * question answered badly: nothing could establish that what answers the behavior was built against
 * the module the row is written for, so the row was not handed on at all. Both are
 * {@code FIXTURES_VALIDATED}/{@code INCOMPLETE}, because in both nothing about the model was
 * established and nothing applied the row.
 *
 * <p>What a host was supposed to provide and did not — the runtime off the classpath, so the
 * generated classes will not link — is still said of the module rather than of a row
 * ({@link Incompleteness}).
 *
 * <p>Whether the behavior was applied is the {@link Stage} column: everything at {@code INVOKED} or
 * past it says what applied it ({@link Run#applied()}), and everything before it says nothing did.
 * What the row counted is a different question and is not read off this table — a row that stopped
 * at {@code NONE} spent whatever its fixtures spent, and a row given up on was never read at all
 * ({@link Counting}).
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
 * @param run            what applied the behavior, and what this compile counted while the row ran.
 *                       A row that reached {@link Stage#INVOKED} says what applied it and a row that
 *                       did not says nothing did, which is held to at construction: the two are
 *                       different cuts of one evaluation and cannot be recorded disagreeing. What
 *                       the counting says is not held to the stage, because a row's evaluation is
 *                       not only its application — a fixture applies the helpers it names first, so
 *                       a row that applied nothing can still have spent counted points
 */
public record RowOutcome(SourcePos at,
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
        java.util.Objects.requireNonNull(run, "a row says what became of its evaluation");
        if (stage.reached(Stage.INVOKED) == run.applied() instanceof Applied.Nothing) {
            // Held here because the two are written from one evaluation and read apart: a stage that
            // says the behavior was applied and a run that says nothing applied it is a state no
            // evaluation produces, and a reader that met it would have to decide which half to trust.
            // What the row counted is not held to the stage — a fixture spends counted points before
            // the behavior is reached, and a row that never reached it spent what it spent.
            throw new IllegalArgumentException(
                    "a row that applied the behavior says what applied it, and one that did not says "
                            + "nothing did: " + stage + " with " + run.applied());
        }
    }

    /** Whether the behavior answered for this row — it was applied and a value came back, which is
     * what {@link Stage#COMPARED} is reached by. Whether that answer can be named as a case is
     * {@link #observed}: a value of a type no declaration of the module's names is an answer all the
     * same, and a run that got one is not a run that produced nothing. */
    public boolean answered() {
        return stage.reached(Stage.COMPARED);
    }

    /** Whether this row is evidence that the behavior can answer with {@link #resultArm}. A row that
     * disagreed still saw what it saw. */
    public boolean observed() {
        return answered() && resultArm != null;
    }
}
