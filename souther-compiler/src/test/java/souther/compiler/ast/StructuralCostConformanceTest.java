package souther.compiler.ast;

import org.junit.jupiter.api.Test;
import souther.compiler.frontend.CstFrontend;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the language says a construct costs, and what this compiler builds for it, are the same
 * number.
 *
 * <p>Two constructs do not survive being built: a block becomes a spine of bindings, and a pattern
 * becomes the bindings it takes out of a value. Both have an algebra of their own in the
 * specification, and neither can be read back off what folding it left — which is why {@code
 * StructuralCost} may measure a tree at all. It may because the folds are required to write exactly
 * what the rules say those constructs cost, and this is where that is required.
 *
 * <p>So a fold that changed shape fails here rather than quietly moving what compiles. What to do
 * about it is one of two things and this says which: either the fold no longer writes what the rule
 * says, or the rule no longer says what the language means.
 */
class StructuralCostConformanceTest {

    /** What a body of {@code written} costs, built the way the compiler builds it. */
    private static int built(String declarations, String parameter, String written) {
        String source = "module m exposing (f%s)\n\n%sbehavior f : (r: %s) -> Int\nlet f (%s) = %s\n"
                .formatted(declarations.isEmpty() ? "" : ", R",
                        declarations.isEmpty() ? "" : declarations + "\n\n",
                        parameterType(declarations), parameter, written);
        Ast.Module m = CstFrontend.parse(source);
        Ast.FnDef fn = m.fns().stream().filter(d -> d.written().spelling().equals("f")).findFirst()
                .orElseThrow();
        return StructuralCost.of(((Ast.FnBody.Written) fn.body()).expr());
    }

    private static String parameterType(String declarations) {
        return declarations.isEmpty() ? "(Int, Int, Int)" : "R";
    }

    private record Pattern(String written, String declarations, int binds) {}

    /**
     * A pattern on its own is one deeper than it binds: the bindings, and taking a part out of the
     * value. A name, which takes nothing apart, costs nothing beyond itself.
     *
     * <p>This is the pattern's own depth, which is not what it encloses. Taking a part out is on
     * the part and not on what comes after the pattern — {@link #aBlockStatementCostsTheStepsItTakes}
     * is the other number, and a destructuring statement encloses what follows it in the bindings
     * alone.
     */
    @Test
    void aPatternIsOneDeeperThanItBinds() {
        String three = "data R = { f0: String, f1: String, f2: String }";
        String eight = "data R = { f0: String, f1: String, f2: String, f3: String, f4: String,"
                + " f5: String, f6: String, f7: String }";
        List<Pattern> patterns = List.of(
                new Pattern("(a, b)", "", 3),
                new Pattern("(a, b, c)", "", 4),
                new Pattern("((a, b), c)", "", 5),
                new Pattern("{ f0 }", "data R = { f0: String }", 2),
                new Pattern("{ f0, f1, f2 }", three, 4),
                new Pattern("{ f0, f1, f2, f3, f4, f5, f6, f7 }", eight, 9),
                new Pattern("N(v)", "data N = Int", 2));

        for (Pattern pattern : patterns) {
            String type = pattern.declarations().startsWith("data N") ? "N"
                    : parameterType(pattern.declarations());
            int taken = builtWith(pattern.declarations(), type, pattern.written());
            int name = builtWith(pattern.declarations(), type, "r");

            assertEquals(name + pattern.binds() + 1, taken,
                    pattern.written() + " binds " + pattern.binds() + " and is taken apart once");
        }
    }

    private static int builtWith(String declarations, String type, String parameter) {
        String exposed = declarations.isEmpty() ? "" : ", " + (type.equals("N") ? "N" : "R");
        String source = "module m exposing (f%s)\n\n%sbehavior f : (r: %s) -> Int\nlet f (%s) = 1\n"
                .formatted(exposed, declarations.isEmpty() ? "" : declarations + "\n\n", type,
                        parameter);
        Ast.Module m = CstFrontend.parse(source);
        Ast.FnDef fn = m.fns().stream().filter(d -> d.written().spelling().equals("f")).findFirst()
                .orElseThrow();
        return StructuralCost.of(((Ast.FnBody.Written) fn.body()).expr());
    }

    private record Statement(String what, String written, int steps) {}

    /**
     * A block's statements cost a step each, and a {@code let} written with a pattern costs one per
     * name it binds.
     *
     * <p>The bindings and not one more. What a pattern takes out of a value is written on the part,
     * so it is a level of the pattern and not of what comes after it —
     * {@link #aPatternIsOneDeeperThanItBinds} is that one. Ten destructurings enclose what follows
     * them in thirty levels, not forty.
     */
    @Test
    void aBlockStatementCostsTheStepsItTakes() {
        List<Statement> statements = List.of(
                new Statement("a let", "let a%d = x", 1),
                new Statement("a guard", "guard x > %d else 0", 1),
                new Statement("a tuple destructure", "let (a%d, b%d) = t", 3));

        for (Statement statement : statements) {
            int shorter = blockOf(statement.written(), 4);
            int longer = blockOf(statement.written(), 14);

            assertEquals(statement.steps() * 10, longer - shorter,
                    statement.what() + " takes " + statement.steps() + " step(s)");
        }
    }

    /** What a statement holds is written inside the step it is, so it adds to the steps before it. */
    @Test
    void whatAStatementHoldsAddsToTheStepsBeforeIt() {
        assertEquals(30, blockHolding(250, 50) - blockHolding(250, 20));
        assertEquals(blockHolding(250, 50), blockHolding(270, 30));
    }

    private static int blockOf(String statement, int statements) {
        StringBuilder sb = new StringBuilder("{\n    let t = (x, x)\n");
        for (int i = 0; i < statements; i++) {
            sb.append("    ").append(statement.replace("%d", String.valueOf(i))).append("\n");
        }
        return built("", "x", sb.append("    x\n}").toString());
    }

    /** A block of {@code steps} guards whose result nests {@code held} deep. */
    private static int blockHolding(int steps, int held) {
        StringBuilder sb = new StringBuilder("{\n");
        for (int i = 0; i < steps; i++) {
            sb.append("    guard x > ").append(i).append(" else 0\n");
        }
        return built("", "x", sb.append("    x").append(" + 1".repeat(held - 1)).append("\n}")
                .toString());
    }
}
