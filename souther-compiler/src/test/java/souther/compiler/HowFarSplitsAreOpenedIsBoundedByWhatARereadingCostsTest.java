package souther.compiler;

import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How far the case splits down one path are opened, bounded by what re-reading a body costs.
 *
 * <p>The bound is a number of readings and not of splits. An {@code if} has two arms and a
 * {@code match} has one per case, so a bound written as a count of splits names one cost for the
 * first and quite another for the second — and what it is protecting against is the readings.
 *
 * <p>Both ends of it are held here: a path that stays inside the bound is opened all the way, and
 * one that would go past it is not, and the two differ in the width of a split and not in what is
 * written after it. What is asked of a split is what opening it <em>would</em> cost, which is what
 * keeps a path already fifteen readings long from admitting a split of any width there is.
 */
class HowFarSplitsAreOpenedIsBoundedByWhatARereadingCostsTest {

    private static String sum(String name, int cases, String prefix) {
        StringBuilder s = new StringBuilder();
        for (int i = 1; i <= cases; i++) {
            s.append("data ").append(prefix).append(i).append("\n");
        }
        s.append("data ").append(name).append(" =");
        for (int i = 1; i <= cases; i++) {
            s.append(i == 1 ? " " : " | ").append(prefix).append(i);
        }
        return s.append("\n").toString();
    }

    /** A match every arm of which answers nought, so what opening it establishes is that nought and
     * reading it costs one reading of the body per case. */
    private static String pick(String name, String type, int cases, String prefix) {
        StringBuilder s = new StringBuilder("let ").append(name)
                .append(" (k: ").append(type).append("): Int =\n    match k with\n");
        for (int i = 1; i <= cases; i++) {
            s.append("        | ").append(prefix).append(i).append(" -> 0\n");
        }
        return s.toString();
    }

    private static final String TYPES = """
            module demo

            data Big = Int
                invariant big = value >= 1000

            """
            + sum("Two", 2, "T") + sum("Eight", 8, "E") + sum("Nine", 9, "N")
            + pick("two", "Two", 2, "T")
            + pick("eight", "Eight", 8, "E")
            + pick("nine", "Nine", 9, "N");

    private static boolean owed(String body) {
        return Compiler.compileWithWarnings(TYPES + "\n" + body).warnings().stream()
                .anyMatch(d -> d.severity() == Severity.WARNING && "E2011".equals(d.code()));
    }

    /** Four nested conditionals are sixteen readings of the body, which is the whole of the bound. */
    @Test
    void fourNestedConditionalsAreOpened() {
        assertFalse(owed("""
                behavior use : (a: Int, b: Int, c: Int, d: Int) -> Big
                    constructs Big
                let use (a, b, c, d) = Big(1000
                    + (if a > 0 then 0 else 0)
                    + (if b > 0 then 0 else 0)
                    + (if c > 0 then 0 else 0)
                    + (if d > 0 then 0 else 0))
                """), "sixteen readings is what four of them cost, and sixteen is the bound");
    }

    /** A fifth is thirty-two, which is past it, so what it puts in is a value nothing says anything
     * about. */
    @Test
    void aFifthConditionalIsNotOpened() {
        assertTrue(owed("""
                behavior use : (a: Int, b: Int, c: Int, d: Int, e: Int) -> Big
                    constructs Big
                let use (a, b, c, d, e) = Big(1000
                    + (if a > 0 then 0 else 0)
                    + (if b > 0 then 0 else 0)
                    + (if c > 0 then 0 else 0)
                    + (if d > 0 then 0 else 0)
                    + (if e > 0 then 0 else 0))
                """), "a fifth would be thirty-two readings of the body");
    }

    /** A match of any width is opened where it is the first split on the path: refusing it would
     * leave a sum of more cases than the bound read nowhere, which is what the reading is for. */
    @Test
    void aSplitIsOpenedWhereverThePathHasNotMultipliedYet() {
        assertFalse(owed("""
                behavior use : (k: Nine) -> Big
                    constructs Big
                let use (k) = Big(1000 + nine(k))
                """), "nine readings, and nothing had been read twice before it");
    }

    /** Eight readings spent and a conditional after it is sixteen, which is the bound — so a
     * conditional inside an arm of a sum this wide is opened, as it was when a match was not read
     * here at all and the conditional was lifted out of the arm instead. */
    @Test
    void aConditionalAfterAWideMatchIsOpenedWhereItStaysInsideTheBound() {
        assertFalse(owed("""
                behavior use : (k: Eight, a: Int) -> Big
                    constructs Big
                let use (k, a) = Big(1000 + eight(k) + (if a > 0 then 0 else 0))
                """), "eight readings times two is sixteen, and sixteen is the bound");
    }

    /** One case more and it is eighteen, which is past it. */
    @Test
    void aSplitThatWouldTakeThePathPastTheBoundIsNotOpened() {
        assertTrue(owed("""
                behavior use : (k: Nine, a: Int) -> Big
                    constructs Big
                let use (k, a) = Big(1000 + nine(k) + (if a > 0 then 0 else 0))
                """), "nine readings times two is eighteen, and eighteen is past sixteen");
    }

    /** The same program with two readings spent instead of nine, so what stopped the one above was
     * the width of the split before it. */
    @Test
    void theSameSplitIsOpenedWhereLessOfTheBoundWasSpent() {
        assertFalse(owed("""
                behavior use : (k: Two, a: Int) -> Big
                    constructs Big
                let use (k, a) = Big(1000 + two(k) + (if a > 0 then 0 else 0))
                """), "two readings times two is four, and four is inside sixteen");
    }
}
