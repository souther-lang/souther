package souther.compiler.check;

/**
 * The canonical statement a comparison comes to, over two values of whatever a reader holds them
 * as.
 *
 * <p>Six ways to compare two values state three things between them: that the two are the same
 * value, that one stands below the other, and the denial of either. Which of the three a comparison
 * states is decided from what it placed ({@link ComparisonClaim}), and it is decided once — a
 * reader that worked it out from the operator would be a second answer, and the two agree only for
 * as long as somebody keeps them so.
 *
 * <p><b>A proposition and not a record of one.</b> Nothing here can be taken apart. Which of the
 * three this is, which side each value is on, and whether it is denied are what a reader would have
 * to put back together, and putting them back together is the derivation this type exists to hold:
 * a reader that switched on the first fact and forgot the last would state the comparison that
 * holds exactly where this one does not. So the only way to read one is {@link #expressedAs}, which
 * hands the reader its own three constructors and assembles the answer here.
 *
 * <p><b>Over any two values.</b> A comparison of two terms and a comparison of two expressions
 * state the same thing about their sides, and what differs is only what a side is and what a
 * statement about two of them is written as. So the values are the reader's, and so is what comes
 * back.
 */
final class CanonicalComparison<A> {

    /** How a reader writes the three statements in its own representation. */
    interface Expression<A, T> {

        /** The two sides are the same value. */
        T theSameValue(A left, A right);

        /** The left side stands below the right. */
        T below(A left, A right);

        /** What holds exactly where {@code statement} does not. */
        T denied(T statement);
    }

    private final Statement<A> statement;

    private CanonicalComparison(Statement<A> statement) {
        this.statement = statement;
    }

    /** The statement that the two sides are the same value. */
    static <A> CanonicalComparison<A> theSameValue(A left, A right) {
        return new CanonicalComparison<>(new Same<>(left, right));
    }

    /** The statement that {@code left} stands below {@code right}. */
    static <A> CanonicalComparison<A> below(A left, A right) {
        return new CanonicalComparison<>(new Below<>(left, right));
    }

    /** What holds exactly where this does not. */
    CanonicalComparison<A> denied() {
        return new CanonicalComparison<>(new Denied<>(statement));
    }

    /** This statement, written by {@code expression} in the reader's own representation. */
    <T> T expressedAs(Expression<A, T> expression) {
        return statement.expressedAs(expression);
    }

    /** What is stated, kept where no reader can name it. */
    private sealed interface Statement<A> {

        <T> T expressedAs(Expression<A, T> expression);
    }

    private record Same<A>(A left, A right) implements Statement<A> {

        @Override
        public <T> T expressedAs(Expression<A, T> expression) {
            return expression.theSameValue(left, right);
        }
    }

    private record Below<A>(A left, A right) implements Statement<A> {

        @Override
        public <T> T expressedAs(Expression<A, T> expression) {
            return expression.below(left, right);
        }
    }

    private record Denied<A>(Statement<A> of) implements Statement<A> {

        @Override
        public <T> T expressedAs(Expression<A, T> expression) {
            return expression.denied(of.expressedAs(expression));
        }
    }
}
