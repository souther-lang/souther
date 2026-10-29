package souther.compiler.coverage;

/**
 * Why the measuring classes carry no switch at a walk, so that no run is the walk rewritten there.
 *
 * <p>A walk the language owes a row of is owed one whether or not this compiler can write the walk
 * rewritten, and a walk it cannot write that way is not one it concludes anything of: the rewrites
 * of it stay open and say why.
 */
public sealed interface NotCarriedReason {

    /**
     * Whether a run that went through the walk would have recorded taking a second element of it,
     * which is what shows a list that is one list on every run to hold one element at most.
     */
    boolean recordsTheSecondElement();

    /**
     * The method the walk is written in would be more than the JVM holds with the switch in it, so
     * it is written without. The walk is the loop it always is, and a run still records what it
     * went through.
     */
    record MethodTooLarge() implements NotCarriedReason {

        @Override
        public boolean recordsTheSecondElement() {
            return true;
        }
    }

    /**
     * The step is not written where the fold hands it over: it is chosen as the program runs, or
     * reaches the fold as a value. The fold is then run by the library's one method for every call
     * of it, and a rewrite there would be the rewrite of every other fold. A run records only that
     * it reached the fold, and nothing of how far it went.
     */
    record StepNotExpanded() implements NotCarriedReason {

        @Override
        public boolean recordsTheSecondElement() {
            return false;
        }
    }
}
