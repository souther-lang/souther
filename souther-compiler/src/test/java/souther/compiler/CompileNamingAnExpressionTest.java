package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Severity;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Naming an expression does not change what is known about it. This is the property the
 * invariant-discharge check is built on rather than an example of it: whatever the check answers for
 * a construction from an expression, it answers the same for a construction from a name bound to
 * that expression, and from a name bound to that name.
 *
 * <p>Each expression is put through every shape against every target, and the shapes are required to
 * agree with each other — not to give any particular answer. What the check can prove is free to
 * change; that it proves the same thing of one value written two ways is not.
 */
class CompileNamingAnExpressionTest {

    /** The expressions a construction is given, one per row, over the inputs {@link #MODULE} binds. */
    private static final List<String> EXPRESSIONS = List.of(
            "c.value",                              // a location
            "c.value + 1",                          // affine over one
            "c.value * 2",                          // a scalar product
            "c.value * n",                          // a variable product, outside the fragment
            "c.value / 2",                          // an integer divide, outside it too
            "Int.add(c.value, 1)",                  // the function form of an operator
            "Int.subtract(c.value, 1)",
            "Int.modBy(p.value, c.value)",          // a call the check has no rule about
            "Int.max(0, c.value)",
            "Int.modBy(p.value, c.value) + 1",      // one inside arithmetic
            "if n > 0 then c.value else 0",         // a conditional over locations
            "if n > 0 then c.value else n",         // one branch bounded and one not
            "5",                                    // written out
            "List.length(xs)",                      // a size
            "List.length(List.filter(x -> x > 0, xs))");

    /** The types constructed from them: one every non-negative value satisfies, one that wants more. */
    private static final List<String> TARGETS = List.of("Count", "Positive");

    private static final String MODULE = """
            module demo
            data Count = Int
                invariant value >= 0
            data Positive = Int
                invariant value >= 1
            data Small = Int
                invariant value >= 0
            behavior mk : (c: Count, p: Positive, n: Int, xs: List<Int>) -> %s
                constructs %s
            let mk (c, p, n, xs) = %s
            """;

    /** How the same expression is written: in place, given a name, and given a name for that name. */
    private static String inline(String e) {
        return e;
    }

    private static String named(String e) {
        return "{\n        let v = " + e + "\n        %s\n    }";
    }

    /** What the check says, as one string — the code of an error, or how many warnings. */
    private static String said(String source) {
        try {
            Compiler.Compiled c = Compiler.compileWithWarnings(source);
            return "warnings=" + c.warnings().stream()
                    .filter(d -> d.severity() == Severity.WARNING).count();
        } catch (CompileException e) {
            String code = e.diagnostic().code();
            return code == null ? "error: " + e.getMessage() : code;
        } catch (RuntimeException e) {
            return "raised: " + e.getMessage();
        }
    }

    private static String module(String target, String body) {
        return MODULE.formatted(target, target, body);
    }

    private record Row(String expression, String target) {

        @Override
        public String toString() {
            return target + "(" + expression + ")";
        }
    }

    private static List<Row> rows() {
        List<Row> rows = new ArrayList<>();
        for (String e : EXPRESSIONS) {
            for (String target : TARGETS) {
                rows.add(new Row(e, target));
            }
        }
        return rows;
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("rows")
    void namingAnExpressionDoesNotChangeWhatIsKnownOfIt(Row row) {
        String construct = row.target() + "(%s)";
        String written = said(module(row.target(), construct.formatted(inline(row.expression()))));
        String bound = said(module(row.target(),
                named(row.expression()).formatted(construct.formatted("v"))));
        assertEquals(written, bound, "a name for the expression is that expression");
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("rows")
    void aChainOfNamesEndsAtTheExpression(Row row) {
        String construct = row.target() + "(%s)";
        String written = said(module(row.target(), construct.formatted(inline(row.expression()))));
        String chained = said(module(row.target(), "{\n        let v = " + row.expression()
                + "\n        let w = v\n        let y = w\n        " + construct.formatted("y")
                + "\n    }"));
        assertEquals(written, chained, "each name is what it was given, down the chain");
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("rows")
    void aGuardOnTheExpressionReadsTheSameAsAGuardOnItsName(Row row) {
        // The guard states the same thing of the same value either way, so it settles the same clause
        String construct = row.target() + "(%s)";
        String written = said(module(row.target(), "{\n        guard (" + row.expression()
                + ") >= 1 else Small(0)\n        " + construct.formatted(row.expression()) + "\n    }")
                .replace("constructs " + row.target(), "constructs " + row.target() + ", Small")
                .replace("-> " + row.target(), "-> " + row.target() + " | Small"));
        String bound = said(module(row.target(), "{\n        let v = " + row.expression()
                + "\n        guard v >= 1 else Small(0)\n        " + construct.formatted("v")
                + "\n    }")
                .replace("constructs " + row.target(), "constructs " + row.target() + ", Small")
                .replace("-> " + row.target(), "-> " + row.target() + " | Small"));
        assertEquals(written, bound, "one value, one guard, one answer");
    }
}
