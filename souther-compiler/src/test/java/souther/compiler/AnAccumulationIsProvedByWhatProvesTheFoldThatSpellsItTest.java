package souther.compiler;

import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A total written {@code List.sum} answers what the fold that spells it out answers, and is proved
 * by what proves that fold (spec §invariant-discharge-reduction).
 *
 * <p>{@code List.sum} and {@code List.product} are primitives over a numeric element (ADR-0082), and
 * the only walk the discharge check read was one it was handed a step and a seed for. So a total
 * written as a fold was read and the same total written with the library's own function was a value
 * nothing was known about — the library being the expensive way to write something (#963).
 *
 * <p>Every case here is one total written both ways. What proves it is the same procedure either
 * way: the accumulation is made into the walk it means — an identity, an accumulator, an element,
 * and one step over the two — and {@code InductiveBounds} is asked, which knows no operation's name.
 * The neighbours that stay reported say the walk is being proved rather than credited.
 */
class AnAccumulationIsProvedByWhatProvesTheFoldThatSpellsItTest {

    private static final String TYPES = """
            module demo

            data U = Int
                invariant nonNeg = value >= 0

            data AtLeastOne = Int
                invariant one = value >= 1

            data Money = Int
                invariant nonNeg = value >= 0
            """;

    private static boolean owedIn(String source) {
        return Compiler.compileWithWarnings(source).warnings().stream()
                .anyMatch(d -> d.severity() == Severity.WARNING && "E2011".equals(d.code()));
    }

    private static boolean owed(String expression) {
        Compiler.Compiled compiled = Compiler.compileWithWarnings(TYPES + "\n" + """
                behavior total : (xs: List<U>, ns: List<Int>, ones: List<AtLeastOne>) -> Money
                    constructs Money

                let total (xs, ns, ones) = Money(%s)
                """.formatted(expression));
        return compiled.warnings().stream()
                .anyMatch(d -> d.severity() == Severity.WARNING && "E2011".equals(d.code()));
    }

    /** The two lines the issue is about: a total of the same amounts, written with the library's
     * function and written out as the walk it is. */
    @Test
    void aSumOfWhatAMapBuiltIsTheFoldThatSpellsItOut() {
        assertFalse(owed("List.sum(List.map(x -> x.value, xs))"),
                "a sum of numbers at or above nought is at or above nought");
        assertFalse(owed("List.fold((acc, x) -> acc + x, 0, List.map(x -> x.value, xs))"),
                "which is what the fold saying the same thing answers");
    }

    /** The elements written on the line bound the accumulation as they bound the fold: the seed is
     * the identity the operation starts from, and nothing was expanded to find it. */
    @Test
    void aSumOfElementsWrittenOutIsBoundedByThem() {
        assertFalse(owed("List.sum([1, 2, 3])"));
        assertFalse(owed("List.fold((acc, x) -> acc + x, 0, [1, 2, 3])"));
    }

    /** And a sum over elements nothing bounds is reported, both ways round — a walk over numbers
     * that may be below nought answers something that may be below nought. */
    @Test
    void aSumOverElementsNothingBoundsIsOwed() {
        assertTrue(owed("List.sum(ns)"));
        assertTrue(owed("List.fold((acc, x) -> acc + x, 0, ns)"));
    }

    /**
     * The other primitive, whose step is a product.
     *
     * <p>A product is not a form, so what the step answers is an atom standing for one, recorded
     * against the recipe that says what it is — the same recipe the naming makes of a product
     * written into a fold's step. Under the induction hypothesis both operands are bounded and the
     * recipe answers a range, which is how one line proves the other.
     */
    @Test
    void aProductIsProvedWhereTheFoldThatSpellsItOutIs() {
        assertFalse(owed("List.product(List.map(x -> x.value, ones))"),
                "a product of numbers at or above one, started at one, stays at or above one");
        assertFalse(owed("List.fold((acc, x) -> acc * x.value, 1, ones)"),
                "which is what the fold saying the same thing answers");
        assertFalse(owed("List.product([2, 3])"));
    }

    /**
     * And the same over the other kind of number the domain carries.
     *
     * <p>What an accumulation starts from is a recipe read at the type the call answers (ADR-0082),
     * so {@code List.sum} of decimals starts from a nought that is a {@code Decimal} — not from a
     * literal written into a tree for its type to be inferred off again. The two places of the walk
     * are named with that type's spacing for the same reason, so a range asserted about the
     * accumulator is one the domain takes.
     */
    @Test
    void anAccumulationOfDecimalsIsTheWalkItMeansAsAnAccumulationOfWholeNumbersIs() {
        String decimals = """
                module demo

                data Rate = Decimal
                    invariant nonNeg = value >= 0.0m

                data Summed = Decimal
                    invariant nonNeg = value >= 0.0m

                behavior walkIt : (ds: List<Rate>) -> Summed
                    constructs Summed
                let walkIt (ds) = Summed(%s)
                """;
        assertFalse(owedIn(decimals.formatted("List.sum(List.map(x -> x.value, ds))")),
                "a sum of decimals at or above nought is at or above nought");
        assertFalse(owedIn(decimals.formatted(
                        "List.fold((acc, x) -> acc + x.value, 0.0m, ds)")),
                "which is what the fold saying the same thing answers");
        assertFalse(owedIn(decimals.formatted("List.product(List.map(x -> x.value, ds))")),
                "and a product of them, started at one, never leaves them");
    }

    /** And a product over elements nothing bounds is reported, as its fold is. */
    @Test
    void aProductOverElementsNothingBoundsIsOwed() {
        assertTrue(owed("List.product(ns)"));
        assertTrue(owed("List.fold((acc, x) -> acc * x, 1, ns)"));
    }
}
