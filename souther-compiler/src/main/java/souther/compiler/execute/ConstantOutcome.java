package souther.compiler.execute;

import java.util.Optional;

/**
 * What became of running one constant construction's check.
 *
 * <p>Three and not two. The third was in the code already, as the {@code continue} of a caught
 * {@code ReflectiveOperationException | LinkageError}: where the check cannot be loaded or run at
 * compile time, the construction is left to the check that runs when the program does (ADR-0032).
 * Written as control flow inside the one caller, that was a decision the language made wearing the
 * shape of an error being swallowed — and a reader of the answer could not tell a constant that
 * held from one nobody asked about.
 */
public sealed interface ConstantOutcome {

    /** The value satisfies the invariant. */
    record Holds() implements ConstantOutcome {}

    /**
     * The value does not satisfy the invariant, and which clause it is that it fails.
     *
     * <p>Empty where the clause carries no name of its own. What is reported is then that the
     * invariant is violated rather than which part of it, which is what a construction at run time
     * would say of the same value.
     */
    record Violates(Optional<String> clause) implements ConstantOutcome {

        public Violates {
            if (clause == null) {
                throw new IllegalArgumentException("a violation either names a clause or does not");
            }
        }
    }

    /**
     * Not decided here, and the check that runs when the program does still applies.
     *
     * <p>Carries no reason. Whether the class would not load, would not verify, or has no check to
     * call are three ways of arriving at one language state, and a compile does the same thing in
     * all three. A reason here would be the machine's account of its own failure, offered where the
     * language asked a question about a program.
     */
    record NotEvaluatedHere() implements ConstantOutcome {}
}
