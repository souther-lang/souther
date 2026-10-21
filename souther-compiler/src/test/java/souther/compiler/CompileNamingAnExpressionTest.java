package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Severity;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

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
 * <p>Each expression is put through every shape against every target — named down a chain of names,
 * and named under a guard — and each shape is required to agree with the expression written in
 * place, not to give any particular answer. What the check can prove is free to
 * change; that it proves the same thing of one value written two ways is not.
 */
class CompileNamingAnExpressionTest {

    /** The expressions a construction is given, one per row, over the inputs {@link #MODULE} binds. */
    private static final List<String> EXPRESSIONS = List.of(
            "c.value",                              // a location
            "c.value + 1",                          // affine over one
            "c.value * 2",                          // a scalar product
            "c.value * n",                          // a variable product, outside the fragment
            "c.value * n + 1",                      // one inside arithmetic the fragment does read
            "c.value / 2",                          // an integer divide, outside it too
            "Int.add(c.value, 1)",                  // the function form of an operator
            "Int.subtract(c.value, 1)",
            "Int.floorMod(c.value, p.value)",          // a call the check has no rule about
            "Int.max(0, c.value)",
            "Int.floorMod(c.value, p.value) + 1",      // one inside arithmetic
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

    /**
     * What the invariant-discharge check says, as one string — the code of an error, or how many of
     * its warnings.
     *
     * <p>Its own warnings and no other check's. Whether a branch is reached is a fact about the
     * source as written, and an expression written twice is two branches where a name for it is
     * evaluated once: a guard that rules out the second copy's other arm makes that arm dead, which
     * a name has no copy of.
     *
     * <p>So the check is what is asked, over the bodies it reads, and not the classes or the other
     * warnings of the module: an error the check or anything it reads raises is the failure, and
     * its warnings are what is counted.
     */
    private static String said(String source) {
        try {
            Compilation compilation = Compilation.ofSource(source, ImplicitModuleName.OF_A_TEXT);
            CompileException structural = compilation.structuralFailure();
            if (structural != null) {
                throw structural;
            }
            for (String module : compilation.modules()) {
                compilation.db().ask(new Bodies.InvariantWarnings(module));
            }
            CompileException failure = compilation.failure();
            if (failure != null) {
                throw failure;
            }
            return "warnings=" + compilation.warnings().stream()
                    .filter(d -> d.diagnostic().severity() == Severity.WARNING)
                    .filter(d -> "E2011".equals(d.diagnostic().code())).count();
        } catch (CompileException e) {
            String code = e.diagnostic().code();
            return code == null ? "error: " + e.getMessage() : code;
        } catch (RuntimeException e) {
            return "raised: " + e.getMessage();
        }
    }

    /** {@code source} with the guard's departure added to what the behavior answers and builds. */
    private static String departing(String target, String source) {
        return said(source.replace("constructs " + target, "constructs " + target + ", Small")
                .replace("-> " + target, "-> " + target + " | Small"));
    }

    private static String module(String target, String body) {
        return MODULE.formatted(target, target, body);
    }

    record Row(String expression, String target) {

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

    /**
     * A name for the expression, a name for that name and a name for that one, each read as what it
     * was given: the first name is the expression, and each after it is the name before it, so a
     * name that read less than the expression would leave the end of the chain reading less too.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("rows")
    void aChainOfNamesEndsAtTheExpression(Row row) {
        String construct = row.target() + "(%s)";
        String written = said(module(row.target(), construct.formatted(row.expression())));
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
        String written = departing(row.target(), module(row.target(), "{\n        guard ("
                + row.expression() + ") >= 1 else Small(0)\n        "
                + construct.formatted(row.expression()) + "\n    }"));
        String bound = departing(row.target(), module(row.target(), "{\n        let v = "
                + row.expression() + "\n        guard v >= 1 else Small(0)\n        "
                + construct.formatted("v") + "\n    }"));
        assertEquals(written, bound, "one value, one guard, one answer");
    }

    /** Values written into the source rather than computed: what a name for one has to carry is not
     * a key but the text, since what a clause reading it says is decided by folding that text. */
    private static final List<String> WRITTEN = List.of(
            "Code(%s)|\"12\"",
            "Code(%s)|\"ab\"",
            "Table(%s)|[ Row { grade = 1 }, Row { grade = 2 } ]",
            "Table(%s)|[ ]",
            "Wrapped(%s)|Row { grade = 1 }",
            "Wrapped(%s)|row(1)");

    private static final String WRITTEN_MODULE = """
            module demo
            data Code = String
                invariant String.matches("[0-9][0-9]", value)
            data Row = { grade: Int }
            data Table = List<Row>
                invariant List.length(value) >= 1
            data Wrapped = { of: Row }
                invariant of.grade >= 1
            let row (n: Int) = Row { grade = n }
            behavior mk : (x: Int) -> %s
                constructs Code, Table, Wrapped, Row
            let mk (x) = %s
            """;

    private static List<String> written() {
        return WRITTEN;
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("written")
    void namingAWrittenValueDoesNotChangeWhatIsKnownOfIt(String row) {
        String construct = row.split("\\|")[0];
        String value = row.split("\\|")[1];
        String target = construct.substring(0, construct.indexOf('('));
        String inline = WRITTEN_MODULE.formatted(target, construct.formatted(value));
        String bound = WRITTEN_MODULE.formatted(target,
                "{\n        let v = " + value + "\n        " + construct.formatted("v") + "\n    }");
        assertEquals(kindOf(said(inline)), kindOf(said(bound)),
                "a name for a written value carries what was written");
    }

    /** Whether it was an error or not. Which check named the error is not what is being fixed here:
     * a construction from a value written where it is built is the constant check's to report, and
     * one from a name for that value is this check's, and they word it differently. */
    private static String kindOf(String said) {
        return said.startsWith("warnings=") ? said : "error";
    }
}
