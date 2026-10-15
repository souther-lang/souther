package souther.compiler.coverage;

/**
 * What one number the instrumentation hands out is an address of.
 *
 * <p>Two families under one numbering. An arm and a condition are both places a run is recorded at
 * and both take a number from the one counter, because what records a run is one set of numbers; a
 * number written for an arm and a number written for a condition are told apart by nothing in the
 * number itself. So the numbering says which each was issued to, and says it here.
 *
 * <p>The whole of what a number means, so that a numbering can be held against another one. A number
 * means a place in a body, and a place is where it is rather than which object stood there
 * ({@link NodeAddress}).
 */
public sealed interface SiteAddress {

    /** Where a run through one arm of one fork is recorded.
     *
     * @param part which arm of the fork, in the order the fork holds them */
    record Arm(NodeAddress fork, int part) implements SiteAddress {

        public Arm {
            if (fork == null) {
                throw new IllegalArgumentException("an arm is an arm of a fork somewhere");
            }
            if (part < 0) {
                throw new IllegalArgumentException(
                        "an arm stands somewhere among the fork's: " + part);
            }
        }

        @Override
        public String toString() {
            return "arm " + part + " of " + fork;
        }
    }

    /** Where the way one condition came out is recorded: the node whose value is the condition. A
     *  condition is one value, so there is no part: what a fork holds several of is arms. */
    record ConditionOutcome(NodeAddress at) implements SiteAddress {

        public ConditionOutcome {
            if (at == null) {
                throw new IllegalArgumentException("a condition is one computed somewhere");
            }
        }

        @Override
        public String toString() {
            return "condition at " + at;
        }
    }
}
