package souther.compiler.ast;

import org.junit.jupiter.api.Test;
import souther.compiler.frontend.CstFrontend;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/** The cost is a number over what the source wrote, and it composes. */
class StructuralCostTest {

    /** What a lowered pattern costs besides its bindings: the {@code $t.0} or {@code $r.field} a
     *  binding takes its value from, which is a read off a name. */
    private static final int READING_THE_VALUE_OUT = 2;

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

    /**
     * What a pattern is charged and what lowering it builds are the same number.
     *
     * <p>The charge is counted from the pattern the author wrote — the value and what is taken out
     * of it — and never from the bindings it becomes, so that changing how a pattern is lowered
     * cannot change what compiles. Which leaves one thing to hold: that this lowering writes a
     * level per binding and not more than a fixed amount besides, so that holding the charge holds
     * the walks too.
     *
     * <p>The amount besides is reading the value out. A binding's value is {@code $t.0} or
     * {@code $r.field} — two levels hanging off the spine rather than along it — so the deepest way
     * down a lowered pattern is its bindings and then that, whatever the pattern was. A lowering
     * that wrote a level per binding and nothing else would come in under this, and one that wrote
     * a level per anything else would come in over it.
     */
    @Test
    void aPatternCostsTheBindingsItIntroducesAndLoweringWritesOneLevelEach() {
        record Case(String pattern, String data, int bindings) {}
        List<Case> cases = List.of(
                new Case("(a, b)", null, 3),
                new Case("(a, b, c)", null, 4),
                new Case("{ f0, f1, f2 }", "data R = { f0: String, f1: String, f2: String }", 4),
                new Case("{ f0 }", "data R = { f0: String }", 2));

        for (Case one : cases) {
            String source = "module m exposing (f" + (one.data() == null ? "" : ", R") + ")\n\n"
                    + (one.data() == null ? "" : one.data() + "\n\n")
                    + "behavior f : (r: " + (one.data() == null ? "(Int, Int, Int)" : "R")
                    + ") -> Int\nlet f (" + one.pattern() + ") = 1\n";
            Ast.Module m = CstFrontend.parse(source);
            Ast.FnDef fn = m.fns().stream().filter(d -> d.written().spelling().equals("f"))
                    .findFirst().orElseThrow();
            int built = StructuralCost.of(((Ast.FnBody.Written) fn.body()).expr());

            int levels = built - 1;   // the body under it is the last level
            assertTrue(one.bindings() <= levels && levels <= one.bindings() + READING_THE_VALUE_OUT,
                    "`" + one.pattern() + "` is charged " + one.bindings()
                            + " bindings, and lowering it builds " + levels + " levels");
        }
    }

    /**
     * What a statement is charged and what folding it builds are the same number.
     *
     * <p>A block's steps are charged from the statements the source wrote, and folding them writes
     * a level each — a {@code let} a binding, a {@code guard} the case it settles, a pattern one per
     * name it binds. The charge and the fold agreeing is what lets the count be taken off the
     * folded body: a fold that stopped writing a level per step would leave the count reading
     * something the rule does not say, and this is where that shows.
     */
    @Test
    void aStatementIsChargedOneStepAndFoldingItWritesOneLevel() {
        record Case(String what, String statement, int steps) {}
        List<Case> cases = List.of(
                new Case("a let", "let a%d = x", 1),
                new Case("a guard", "guard x > %d else 0", 1),
                new Case("a tuple destructure", "let (a%d, b%d) = t", 3));

        for (Case one : cases) {
            int shorter = costOfBlock(one.statement(), 4);
            int longer = costOfBlock(one.statement(), 14);

            assertEquals(one.steps() * 10, longer - shorter,
                    one.what() + " is charged " + one.steps() + " step(s), and ten more of them "
                            + "build " + (longer - shorter) + " levels");
        }
    }

    /** A block of {@code statements} of one kind, over a tuple something can be taken out of. */
    private static int costOfBlock(String statement, int statements) {
        StringBuilder sb = new StringBuilder("{\n    let t = (x, x)\n");
        for (int i = 0; i < statements; i++) {
            sb.append("    ").append(statement.replace("%d", String.valueOf(i))).append("\n");
        }
        return costOf(sb.append("    x\n}").toString());
    }

    /**
     * The bound is where the algebra says, and the algebra is over the source.
     *
     * <p>Written as a pair on either side of it, for each way a block can spend what it has: steps
     * alone, and steps with something held at the end of them. What is fixed here is the arithmetic
     * — that the steps a block takes and what its result holds add, and that a step is a step
     * whether or not it binds a name. A `+guard+` binds nothing, so a block of them costing what a
     * block of `+let+`s costs is the whole of what "step" means.
     */
    @Test
    void theBoundIsWhereTheAlgebraPutsIt() {
        assertEquals(1, costOfGuards(200) - costOfGuards(199),
                "one more guard is one more step");
        assertEquals(costOfGuards(100), costOfBlock("let a%d = x", 100),
                "a guard binds nothing and costs what a let costs");

        assertEquals(30, costOfSteppedBlockHolding(250, 50) - costOfSteppedBlockHolding(250, 20),
                "what the result holds is counted from where the result stands, and adds");
        assertEquals(costOfSteppedBlockHolding(250, 50), costOfSteppedBlockHolding(270, 30),
                "steps and what is held at the end of them are the one quantity");
    }

    private static int costOfGuards(int statements) {
        StringBuilder sb = new StringBuilder("{\n");
        for (int i = 0; i < statements; i++) {
            sb.append("    guard x > ").append(i).append(" else 0\n");
        }
        return costOf(sb.append("    x\n}").toString());
    }

    /** A block of {@code steps} guards whose result nests {@code held} deep. */
    private static int costOfSteppedBlockHolding(int steps, int held) {
        StringBuilder sb = new StringBuilder("{\n");
        for (int i = 0; i < steps; i++) {
            sb.append("    guard x > ").append(i).append(" else 0\n");
        }
        return costOf(sb.append("    x").append(" + 1".repeat(held - 1)).append("\n}").toString());
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
