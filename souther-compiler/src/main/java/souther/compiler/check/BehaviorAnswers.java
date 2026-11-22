package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.ValueName;

import java.util.Optional;

/**
 * What a reader of a body asks of the bodies beside it: the body of each recursive helper as a
 * call of it is read ({@link ARecursion}), with the parameters standing for what the call handed,
 * and which constructions are shown to hold where they are made.
 *
 * <p>A recursive helper is the one helper a call in an analysed body is left standing for: every
 * other helper was expanded where it was called. A call of a behavior is a value a run works out,
 * and no body of one is read where the call stands.
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
