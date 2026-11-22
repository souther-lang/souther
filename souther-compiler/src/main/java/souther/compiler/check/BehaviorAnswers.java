package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.ValueName;

import java.util.Optional;

/**
 * What a reader of a body asks of the bodies beside it: the body of each recursive helper as a
 * call of it is read ({@link ARecursion}), with the parameters standing for what the call handed,
 * whether the runs of rows get past a behavior called, and which constructions are shown to hold where
 * they are made.
 *
 * <p>A recursive helper is the one helper a call in an analysed body is left standing for: every
 * other helper was expanded where it was called. A call of a behavior is a value a run works out,
 * and no body of one is read where the call stands. What its caller is told of the body is whether
 * the runs of rows get past it, which is asked of the behavior over its own inputs.
 *
 * <p>Empty where there is no such body: a helper whose parameters declare no types.
 */
public interface BehaviorAnswers {

    /** No body, and no construction shown to hold — for a reading that asks of neither. */
    BehaviorAnswers NONE = new BehaviorAnswers() {

        @Override
        public Optional<ARecursion> recursionOf(ValueName.Helper recursion) {
            return Optional.empty();
        }

        @Override
        public boolean rowsRunsGetPast(ValueName.Behavior behavior) {
            return false;
        }

        @Override
        public boolean builtWhereItsModuleIsBuilt(String module, SourcePos construction) {
            return false;
        }

        @Override
        public boolean shownToHold(String module, Core.Construct made) {
            return false;
        }
    };

    /** The body of the recursive helper {@code recursion} as a call of it is read, with what it
     *  walks, where it has one. */
    Optional<ARecursion> recursionOf(ValueName.Helper recursion);

    /**
     * Whether the run of every row is shown to get past working out the body of {@code behavior},
     * over whatever its inputs may hold. Not that it answers every run there is: a run of a row is
     * taken to get past where the representation stops, as it is past an operation, and the stop
     * there is said in the account of the body whose operation it is. False where there is no body
     * to ask, one injected from outside the model included: that it was not shown to answer is not
     * that it was shown to stop.
     */
    boolean rowsRunsGetPast(ValueName.Behavior behavior);

    /**
     * Whether the construction written at {@code construction} in {@code module} is in a value the
     * compile built, by the code that ships, without breaking an invariant.
     *
     * <p>A value takes nothing and is built where its module builds it, so a construction written
     * in one is built whatever a run is given, and a run reading the value reads one that was
     * built. False where the value could not be built here: that a construction was not shown to
     * hold is not that it was shown not to.
     */
    boolean builtWhereItsModuleIsBuilt(String module, SourcePos construction);

    /**
     * Whether the discharge check, reading the bodies of {@code module}, proved every clause of
     * {@code made} on every reading it made of it ({@link ConstructionsShownToHold}): what holds
     * where it is made keeps every clause, so no run that makes it is refused there. False where
     * the check made no such reading: that a construction was not shown to hold is not that it was
     * shown not to.
     */
    boolean shownToHold(String module, Core.Construct made);
}
