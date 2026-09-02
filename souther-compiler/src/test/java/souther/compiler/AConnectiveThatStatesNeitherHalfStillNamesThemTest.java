package souther.compiler;

import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A value an author wrote about only in a disjunction is one they wrote about.
 *
 * <p>Two things a condition does, and only one of them needs the condition to be read. What a guard
 * <em>establishes</em> is what a proof about the path may rest on, and a disjunction asserted true
 * establishes neither half: one of them holds and the check cannot say which. What a guard
 * <em>names</em> is a different answer, and it is what decides whether a clause over the value is
 * the author's to settle or the run-time check's — a construction over a value nothing has ever
 * mentioned is one no guard they could write would settle, so reporting it would be reporting this
 * compiler's reach as their omission.
 *
 * <p>So the halves of a disjunction go into what the path has spoken of, and nothing else on the
 * walk will put them there: neither half is read, because reading one would be claiming what the
 * connective does not state.
 *
 * <p>Written here because the reading that arrives at a comparison and the reading that arrives at
 * a connective became two ({@link souther.compiler.check.StatedComparison}), and this answer belongs
 * to the second. Held to a construction rather than to what a domain holds, since what it decides is
 * whether the construction is reported at all.
 */
class AConnectiveThatStatesNeitherHalfStillNamesThemTest {

    /** A construction the check has no rule about the value of: {@code String.matches} answers
     *  something no term reads, so whether the clause over it is owed is decided by whether a guard
     *  named it. */
    private static final String MODULE = """
            module demo

            data Ok = Bool
                invariant value
            data Fine

            behavior f : (s: String) -> Ok | Fine
                constructs Ok

            let f (s) = {
                if %s then
                    Ok(String.matches("[0-9]+", s))
                else
                    Fine
            }
            """;

    private static long warningsUnder(String guard) {
        return Compiler.compileWithWarnings(MODULE.formatted(guard)).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING).count();
    }

    /**
     * The construction is reported, because the guard named the value it is built from.
     *
     * <p>Nothing is established of it — the guard holds where either half does — so the clause is
     * owed and unsettled, which is the answer an author can act on by strengthening the guard.
     */
    @Test
    void aDisjunctionNamesBothOfItsHalves() {
        assertEquals(1, warningsUnder(
                "String.matches(\"[0-9]+\", s) || String.matches(\"[a-z]+\", s)"),
                "the construction is over a value the guard named, so the clause it owes is one"
                        + " this check reports rather than leaving to the run time");
    }

    /**
     * And a guard that never names it leaves the construction alone.
     *
     * <p>The pair is what says the first case turns on being named. Both guards establish nothing
     * about what is constructed; they differ in whether the author wrote the value down.
     */
    @Test
    void aGuardThatNamesSomethingElseSaysNothingAboutThisValue() {
        assertEquals(0, warningsUnder("String.matches(\"[a-z]+\", s)"),
                "nothing on this path has mentioned the value, so no guard the author could write"
                        + " would settle the clause and the run-time check stands for it");
    }
}
