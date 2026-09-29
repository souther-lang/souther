package souther.compiler.numeric;

/**
 * A form built up from a handful of atoms and small whole numbers, for a test whose subject is what
 * a domain does with a rule and not what the arithmetic does at the end of its range.
 *
 * <p>Every sum, difference and scaling of such numbers is held, so a chain of them is a form and not
 * an answer that might be one: the chain says {@link #form} at its end and fails, naming which step,
 * where a test was written about numbers that are not small. A test about the range asks
 * {@link LinearForm}'s own operations and reads the answer they give.
 */
public final class SmallForm<A> {

    private final LinearForm<A> form;

    private SmallForm(LinearForm<A> form) {
        this.form = form;
    }

    /** The chain starting from {@code form}. */
    public static <A> SmallForm<A> small(LinearForm<A> form) {
        return new SmallForm<>(form);
    }

    public SmallForm<A> plus(LinearForm<A> other) {
        return new SmallForm<>(form.plus(other).orFail("a sum of small numbers in a test"));
    }

    public SmallForm<A> minus(LinearForm<A> other) {
        return new SmallForm<>(form.minus(other).orFail("a difference of small numbers in a test"));
    }

    public SmallForm<A> times(ExactRatio by) {
        return new SmallForm<>(form.times(by).orFail("a product of small numbers in a test"));
    }

    /** What the chain came to. */
    public LinearForm<A> form() {
        return form;
    }
}
