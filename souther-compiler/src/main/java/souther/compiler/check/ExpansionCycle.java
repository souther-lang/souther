package souther.compiler.check;

/**
 * The expansion was asked to substitute a value it is already substituting.
 *
 * <p>It carries no diagnostic and is not an author's mistake to read. A value defined in terms of
 * itself is one, and it is {@link ValueCycles} that says so — of the module, before anything expands
 * a body of it, at the declaration, once, naming the path the value goes round. That is a statement
 * about the program.
 *
 * <p>This is a statement about the expansion. It is an algorithm with a precondition, and an
 * algorithm handed an input its precondition rules out should fail within a bound rather than descend
 * until the stack runs out — what comes back from that is a report about an expression nesting too
 * deeply, caught at the compiler's outer boundary, by which point which question was being answered
 * is gone. Reaching here means a caller expanded a module nothing had refused, which is the
 * compiler's mistake and not the author's, and it says which value it was standing in.
 *
 * <p>The two do not answer the same question, so neither replaces the other: what recurses under
 * expansion is not what is well founded as a value. A value that reaches itself only through a
 * recursive helper is expanded to the end — the helper is a method and its call is left standing —
 * and evaluating the value still does not terminate. {@link ValueCycles} refuses it; nothing here
 * would notice it.
 */
public final class ExpansionCycle extends RuntimeException {

    ExpansionCycle(String message) {
        super(message);
    }
}
