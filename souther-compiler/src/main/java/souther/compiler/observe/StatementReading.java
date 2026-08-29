package souther.compiler.observe;

/**
 * Whether a module's written statements were read against each other here, and what they said if
 * they were.
 *
 * <p>Two, and the inner answer already has a third thing to say. {@link WrittenStatements.Readings}
 * distinguishes statements that disagreed from statements a reading could not finish in the budget
 * it was given; what it cannot say is that no reading was made at all, which is neither of those and
 * is not a fact about the statements.
 */
public sealed interface StatementReading {

    /** They were read, and this is what they said about each other. */
    record Read(WrittenStatements.Readings said) implements StatementReading {

        public Read {
            if (said == null) {
                throw new IllegalArgumentException("a reading that happened said something");
            }
        }
    }

    /** Nothing was read, so nothing is known about them from here. */
    record NotReadHere() implements StatementReading {}
}
