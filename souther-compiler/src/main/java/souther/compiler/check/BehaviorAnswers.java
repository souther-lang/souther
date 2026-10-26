package souther.compiler.check;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.ValueName;

import java.util.Optional;

/**
 * The body of each behavior, and of each recursive helper, as a call of it is read
 * ({@link CalledBody}), for a reader that reads what a call answers where the call stands, with the
 * parameters standing for what the call handed.
 *
 * <p>A recursive helper is here beside the behaviors because it is the other thing a call in an
 * analysed body is left standing for: every other helper was expanded where it was called.
 *
 * <p>Empty where there is no such body: a behavior with none to read, or one this compilation did
 * not read the input of, and a helper whose parameters declare no types.
 */
public interface BehaviorAnswers {

    /** No body of either — for a reading that reads no call to one. */
    BehaviorAnswers NONE = new BehaviorAnswers() {

        @Override
        public Optional<CalledBody> bodyOf(ValueName.Behavior behavior) {
            return Optional.empty();
        }

        @Override
        public Optional<ARecursion> recursionOf(ValueName.Helper recursion) {
            return Optional.empty();
        }

        @Override
        public boolean builtWhereItsModuleIsBuilt(String module, SourcePos construction) {
            return false;
        }
    };

    /** The body of {@code behavior} as a call of it is read, where it has one. */
    Optional<CalledBody> bodyOf(ValueName.Behavior behavior);

    /** The body of the recursive helper {@code recursion} as a call of it is read, with what it
     *  walks, where it has one. */
    Optional<ARecursion> recursionOf(ValueName.Helper recursion);

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
}
