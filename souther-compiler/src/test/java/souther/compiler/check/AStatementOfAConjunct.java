package souther.compiler.check;

/**
 * A statement of a conjunct named by the number a fixture gives it, for a test that needs a
 * statement to put a line against and is not about numbering.
 *
 * <p>Beside the compiler and not in it: what makes a statement's identity in the compiler is the
 * walk that numbers a conjunct, and nothing there may name one by a number it counted itself.
 */
public final class AStatementOfAConjunct {

    private AStatementOfAConjunct() {}

    /** Statement {@code ordinal} of {@code part}, as an author wrote it. */
    public static InvariantStatementId numbered(PartId<RuleRef.Invariant> part, int ordinal) {
        return new InvariantStatementId(part, StatementNumber.of(ordinal));
    }
}
