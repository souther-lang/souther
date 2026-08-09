package souther.compiler.ast;

import org.junit.jupiter.api.Test;
import souther.compiler.frontend.CstFrontend;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/** The cost is a number over what the source wrote, and it composes. */
class StructuralCostTest {

    private static int costOf(String body) {
        Ast.Module m = CstFrontend.parse("module m exposing (f)\n\n"
                + "behavior f : (x: Int) -> Int\nlet f (x) = " + body + "\n");
        Ast.FnDef fn = m.fns().stream().filter(d -> d.written().spelling().equals("f")).findFirst()
                .orElseThrow();
        return StructuralCost.of(((Ast.FnBody.Written) fn.body()).expr());
    }

    /** A block of {@code statements} bindings, the last of which is {@code value} — the deepest way
     *  down runs through the last one, which is where what a statement holds shows in the total. */
    private static String blockOf(int statements, String value) {
        StringBuilder sb = new StringBuilder("{\n    let a0 = x\n");
        for (int i = 1; i < statements - 1; i++) {
            sb.append("    let a").append(i).append(" = a").append(i - 1).append("\n");
        }
        sb.append("    let a").append(statements - 1).append(" = ").append(value).append("\n");
        return sb.append("    a").append(statements - 1).append("\n}").toString();
    }

    @Test
    void aNameCostsOne() {
        assertEquals(1, costOf("x"));
    }

    @Test
    void nestingCostsOnePerLevel() {
        assertEquals(1 + 4, costOf("x + 1 + 1 + 1 + 1"));
    }

    /** Parentheses group what is written; they are not a construct of their own, and cost nothing. */
    @Test
    void parenthesesCostNothing() {
        assertEquals(costOf("x + 1"), costOf("(((x + 1)))"));
    }

    /** A call this compiler will not splice writes no binding per argument, so it costs what any
     *  other construct costs. What an expanded one costs is asked of the pass that expands it,
     *  which is the only place that knows which calls those are. */
    @Test
    void anApplicationThatIsNotExpandedCostsOne() {
        assertEquals(costOf("g(x)"), costOf("g(x, x, x)"));
    }

    /** Each statement is a binding the ones after it are written inside. */
    @Test
    void aBlockCostsItsStatements() {
        assertEquals(costOf(blockOf(4, "x")) + 6, costOf(blockOf(10, "x")));
    }

    /** The two add: what a statement holds is written inside every statement before it. */
    @Test
    void aBlockAndWhatItHoldsAdd() {
        int statements = 10;
        int nesting = 5;

        assertEquals(costOf(blockOf(statements, "x")) + nesting,
                costOf(blockOf(statements, "x" + " + 1".repeat(nesting))));
    }

    /** Where the deep statement stands does not change the total, and does not add to it twice: the
     *  cost is the longest way down rather than the block's length plus what it holds. */
    @Test
    void whatAStatementHoldsIsCountedFromWhereItStands() {
        String deep = "x" + " + 1".repeat(5);
        String last = blockOf(10, deep);
        String first = last.replace("    let a0 = x\n", "    let a0 = " + deep + "\n")
                .replace("    let a9 = " + deep + "\n", "    let a9 = a8\n");

        assertTrue(costOf(first) < costOf(last),
                "a deep statement at the top is nearer the surface than one at the bottom");
    }

    /** Every definition the language ships is far inside the bound; a bound that the prelude was
     *  already past would be one nothing could be written under. */
    @Test
    void everythingTheLanguageShipsIsWellWithinTheBound() {
        int most = 0;
        String worst = null;
        for (String module : new String[]{"list", "map", "set", "string", "option", "int", "bool",
                "date", "datetime", "decimal"}) {
            Ast.Module m = CstFrontend.parse(read("/souther/" + module + ".sou"));
            for (Ast.FnDef fn : m.fns()) {
                if (fn.body() instanceof Ast.FnBody.Written written) {
                    int cost = StructuralCost.of(written.expr());
                    if (cost > most) {
                        most = cost;
                        worst = module + "." + fn.written().spelling();
                    }
                }
            }
        }
        assertTrue(most * 4 < StructuralCost.MAX,
                "the deepest thing the language ships, " + worst + ", costs " + most
                        + " against a bound of " + StructuralCost.MAX);
    }

    private static String read(String resource) {
        try (java.io.InputStream in = StructuralCostTest.class.getResourceAsStream(resource)) {
            return new String(in.readAllBytes(), java.nio.charset.StandardCharsets.UTF_8);
        } catch (java.io.IOException e) {
            throw new java.io.UncheckedIOException(e);
        }
    }
}
