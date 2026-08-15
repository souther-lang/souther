package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What a construction's reading derives about the arithmetic the domain cannot carry, and what it
 * leaves alone.
 *
 * <p>A recipe — how a product or a truncating quotient was computed — is recorded where the atom is
 * named, and the naming lasts as long as the behavior body being read. What is derived from a recipe
 * depends on what the path assumed, and is answered where a construction is judged. The two are not
 * the same unit, and reading the first as the work list for the second is what made a behavior with
 * many non-linear expressions pay for every one of them at every construction in it.
 *
 * <p>So a reading derives what its own question can reach: the atoms its clauses are decided by, and
 * the atoms the domain it was built from says anything about. The second half is not an optimisation
 * to be tidied away — {@link AProductIsBoundedByWhatThePathBoundsItsFactorsToTest#
 * aClauseReachesAProductThroughAGuardThatEquatesTheTwo} is a clause that names no product and
 * reaches one through a guard that related the two.
 */
class WhatAReadingDerivesIsWhatItsQuestionReachesTest {

    private static final String TYPES = """
            module demo
            data NonNeg = Int
                invariant value >= 0
            data Bad
            """;

    private static List<String> warningsOf(String module) {
        return Compiler.compileWithWarnings(module).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING)
                .map(Diagnostic::code)
                .toList();
    }

    /** The recipes each reading of the module evaluated, by the name each atom renders as. */
    private static List<Set<String>> derivedWhileCompiling(String module) {
        List<List<Term>> watching = new ArrayList<>();
        DerivedBounds.WATCHING = watching;
        try {
            Compiler.compileWithWarnings(module);
        } finally {
            DerivedBounds.WATCHING = null;
        }
        return watching.stream()
                .map(one -> one.stream().map(Term::rendered)
                        .collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new)))
                .map(one -> (Set<String>) one)
                .toList();
    }

    /**
     * One construction, and a behavior around it holding however many products nothing on the path
     * relates to it. What the construction's readings evaluate is the same set every time.
     *
     * <p>The set and not how big it is. A count says the work did not grow; the set says the work is
     * the arithmetic this construction is about, which is the property that stops the growth coming
     * back by another route.
     */
    @Test
    void whatOneConstructionDerivesDoesNotGrowWithArithmeticItIsNotAbout() {
        List<Set<String>> none = derivedWhileCompiling(behaviorWith(0));

        assertFalse(none.isEmpty(), "the construction is over a product, so something was derived");
        assertEquals(none, derivedWhileCompiling(behaviorWith(10)));
        assertEquals(none, derivedWhileCompiling(behaviorWith(100)));
    }

    /** A behavior whose construction is over {@code a * b}, with {@code unrelated} further products
     * bound to names nothing reads. Each is arithmetic the naming records a recipe for, and none of
     * them is a value the clause or the guards reach. */
    private static String behaviorWith(int unrelated) {
        StringBuilder b = new StringBuilder(TYPES);
        b.append("behavior total : (a: Int, b: Int) -> NonNeg | Bad constructs NonNeg, Bad\n");
        b.append("let total (a, b) = {\n");
        b.append("    guard a >= 0\n        else Bad\n");
        b.append("    guard b >= 0\n        else Bad\n");
        for (int i = 0; i < unrelated; i++) {
            b.append("    let n").append(i).append(" = (a + ").append(i)
                    .append(") * (b + ").append(i).append(")\n");
        }
        b.append("    NonNeg(a * b)\n}\n");
        return b.toString();
    }

    /**
     * A bound derived for one recipe is an answer of the reading and not a premise the next recipe is
     * derived from.
     *
     * <p>{@code q == a * b} relates {@code q} to the product through a difference, and
     * {@code NonNeg(q)} is discharged by it — the product's derived bound reaches {@code q} through
     * that difference once it is in. {@code q * c} is a second recipe over {@code q}, and it is
     * derived against the domain the reading was given, in which {@code q} is bounded by nothing. So
     * the clause stands.
     *
     * <p>Held to because it is what makes one pass enough. Were a derived bound readable by another
     * derivation, the answers would depend on the order the recipes were walked in, and deriving from
     * a fixed set of roots would be short of what deriving everything reaches. The control below is
     * the same construction with {@code q} bounded by a guard instead, which is the one difference.
     */
    @Test
    void aBoundDerivedForOneRecipeIsNotReadWhenAnotherIsDerived() {
        assertEquals(List.of(), warningsOf(TYPES + """
                behavior f : (a: Int, b: Int, q: Int) -> NonNeg | Bad constructs NonNeg, Bad
                let f (a, b, q) = {
                    guard a >= 0
                        else Bad
                    guard b >= 0
                        else Bad
                    guard q == a * b
                        else Bad
                    NonNeg(q)
                }
                """));

        assertEquals(List.of("E2011"), warningsOf(TYPES + """
                behavior f : (a: Int, b: Int, c: Int, q: Int) -> NonNeg | Bad constructs NonNeg, Bad
                let f (a, b, c, q) = {
                    guard a >= 0
                        else Bad
                    guard b >= 0
                        else Bad
                    guard c >= 0
                        else Bad
                    guard q == a * b
                        else Bad
                    NonNeg(q * c)
                }
                """));
    }

    /** The control: the same second recipe over a {@code q} a guard bounds directly, so the only
     * difference from the case above is where {@code q}'s bound came from. */
    @Test
    void theSameSecondRecipeIsDerivedWhereTheGuardBoundsItsFactorOutright() {
        assertEquals(List.of(), warningsOf(TYPES + """
                behavior f : (c: Int, q: Int) -> NonNeg | Bad constructs NonNeg, Bad
                let f (c, q) = {
                    guard c >= 0
                        else Bad
                    guard q >= 0
                        else Bad
                    NonNeg(q * c)
                }
                """));
    }

    /**
     * A clause read as the cases of an operation that answers one of its arguments reaches a product
     * standing in one of those cases.
     *
     * <p>Nothing bounds what {@code Int.min} answers, so the clause is not settled as written and is
     * read case by case. The case that answers the product is where the product's derived bound is
     * needed, and the atoms of a case are the case's own to say — a reading that asked only what the
     * clause names as written would leave this construction owed a guard the author has written.
     */
    @Test
    void aClauseReadCaseByCaseReachesAProductStandingInACase() {
        assertEquals(List.of(), warningsOf(TYPES + """
                behavior f : (a: Int, b: Int) -> NonNeg | Bad constructs NonNeg, Bad
                let f (a, b) = {
                    guard a >= 0
                        else Bad
                    guard b >= 0
                        else Bad
                    NonNeg(Int.min(a * b, 100))
                }
                """));
    }
}
