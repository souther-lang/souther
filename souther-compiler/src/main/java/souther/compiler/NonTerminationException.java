package souther.compiler;

/**
 * Evaluating a row did not finish: a `partial` recursion it reaches may not terminate. Reported as its
 * own diagnostic (E1910) rather than hanging the compiler, and named apart from a failing example
 * because nothing was compared.
 */
final class NonTerminationException extends RuntimeException {
    NonTerminationException(String message) {
        super(message);
    }
}
