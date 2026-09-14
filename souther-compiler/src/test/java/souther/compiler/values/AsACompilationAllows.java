package souther.compiler.values;

import souther.compiler.regex.PatternPlan;

/**
 * The allowance a compilation grants a reading, for a test that needs one and is not about it.
 *
 * <p>What governs a reading is handed to it: a compilation chooses the figure and the reading is
 * given the allowance made out of it ({@code Front.Reading}, {@code ReadingPolicy}). A test standing
 * in for the compilation is granting one itself, and this is where it says so — written out at each
 * of them, the tests would be as many places naming the figure as there are tests, and the day one
 * question wanted a different size somebody would be reading them to find out which.
 *
 * <p>Not what a reading may reach. Nothing under {@code souther.compiler.values} grants itself an
 * allowance; the argument for that is in {@link Allowance} and the count of who names the figure is
 * an architecture test's.
 */
public final class AsACompilationAllows {

    private AsACompilationAllows() {
    }

    /** A fresh allowance for every position of one answer, at what a compilation sets. */
    public static <A> Allowance<A> forAdmittedValues() {
        return Allowance.of(admittedValues());
    }

    /** A fresh allowance for handing a position's rules on as the sets they leave. */
    public static <A> Allowance<A> forWhatARuleLeaves() {
        return Allowance.of(whatARuleLeaves());
    }

    /** The figure itself, for a test standing in for the compilation that grants it. */
    public static PatternPlan.Budget admittedValues() {
        return PatternPlan.Budget.OF_ADMITTED_VALUES;
    }

    /** And the other one, which bounds a different question — see the budget's own account. */
    public static PatternPlan.Budget whatARuleLeaves() {
        return PatternPlan.Budget.OF_WHAT_A_RULE_LEAVES;
    }
}
