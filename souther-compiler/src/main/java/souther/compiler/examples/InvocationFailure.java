package souther.compiler.examples;

/**
 * What a generated method ended with, carried out of the invocation that made it.
 *
 * <p>Transport and nothing else. It says that code this compile generated was applied and came back
 * with a {@code cause}, and it says nothing about what that means — not whose failure it is, not
 * whether the row can go on, not which of the things a row does was being done. Those are answered
 * where the row is evaluated, which is what holds the phase it was in and the position it was at.
 *
 * <p>Named for the transport rather than for any of its readings on purpose. A wrapper called a
 * fixture failure or a helper failure would be the reflection that made it deciding what the row is
 * told, which is the shape this exists to remove: the same failure raised through the method a row
 * operand is emitted as and through the method a helper is emitted as arrives here the one way, and
 * the caller assigns the meaning.
 *
 * <p>Not everything a reflective call can end with is one of these. A class that will not load, a
 * method that is not there and an access that is refused are this compiler failing to reach its own
 * output rather than the output failing, and they keep the reading they had.
 */
final class InvocationFailure extends RuntimeException {

    private static final long serialVersionUID = 1L;

    InvocationFailure(Throwable cause) {
        super(cause == null ? "the invocation ended with no cause" : cause.toString(), cause);
    }
}
