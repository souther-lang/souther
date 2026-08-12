package souther.compiler.core;

import souther.compiler.Compiler;
import org.junit.jupiter.api.Test;
import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.ast.StructuralCost;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A source the compiler accepts builds trees its walks can descend.
 *
 * <p>This is the other half of the bound. {@link StructuralCost} says what a definition may say,
 * and the producers of depth hold it — but what makes that worth holding is that everything built
 * from an accepted definition stays within reach of the walks that descend it. That is a property
 * of every transformation there is, present and future, and it is not one a charge at three places
 * can be read off: a pass added later that amplifies what it is handed would break it while every
 * charge still passed.
 *
 * <p>So it is measured rather than argued. Sources are written at the bound, each loading a
 * different producer, and what the compiler built from them is walked and counted — the {@code Ast}
 * after expansion, which is what the checks descend, and the {@code Core} after elaboration, which
 * is what everything below them does.
 *
 * <p>What it holds them to is the bound and not a number of its own. A tree deeper than what the
 * source was allowed to say is a transformation that added depth of its own, which is the thing
 * being watched for; the slack is for the levels a lowering legitimately introduces around what it
 * lowers, which are a constant per construct rather than a count of anything.
 */
class AnAcceptedSourceBuildsOnlyBoundedDepthTest {

    /** What a lowering may add around what it lowers. A behavior's body arrives wrapped in the
     *  bindings its parameters and its {@code depends on} make, and a construction is elaborated
     *  into a few levels where the source wrote one. */
    private static final int SLACK = 64;

    private static String block(int cost) {
        StringBuilder sb = new StringBuilder("module m exposing (f)\n\n"
                + "behavior f : (x: Int) -> Int\nlet f (x) = {\n    let a0 = x\n");
        for (int i = 1; i < cost - 1; i++) {
            sb.append("    let a").append(i).append(" = a").append(i - 1).append("\n");
        }
        return sb.append("    a").append(cost - 2).append("\n}\n").toString();
    }

    private static String valueChain(int cost, int nesting) {
        int names = Math.max(1, (cost - 2) / Math.max(1, nesting));
        StringBuilder sb = new StringBuilder("module m exposing (f)\n\nlet v0 = 1\n");
        for (int i = 1; i <= names; i++) {
            sb.append("let v").append(i).append(" = v").append(i - 1)
              .append(" + 1".repeat(nesting)).append("\n");
        }
        return sb.append("\nbehavior f : (x: Int) -> Int\nlet f (x) = x + v")
                .append(names).append("\n").toString();
    }

    /** A record pattern of {@code fields} names, taken apart in a parameter: what a pattern costs
     *  is the bindings it introduces, and lowering it writes one level each. */
    private static String recordPattern(int fields) {
        StringBuilder sb = new StringBuilder("module m exposing (f, R)\n\ndata R = {\n");
        for (int i = 0; i < fields; i++) {
            sb.append("    f").append(i).append(": String").append(i < fields - 1 ? "," : "").append("\n");
        }
        sb.append("}\n\nbehavior f : (r: R) -> String\nlet f ({ ");
        for (int i = 0; i < fields; i++) {
            sb.append(i == 0 ? "" : ", ").append("f").append(i);
        }
        return sb.append(" }) = f0\n").toString();
    }

    /**
     * A block whose statements take one tuple apart again and again: a binding site that is more
     * than one binding.
     *
     * <p>Each takes the same tuple apart rather than the one before it. A chain that feeds each
     * destructure into the next is exponential in the compiler as it stands (issue #563), which is
     * a size and not a depth — this bound is over the second, and a fixture written the other way
     * would fail here for a reason this is not about.
     */
    private static String destructuringBlock(int statements) {
        StringBuilder sb = new StringBuilder("module m exposing (f)\n\n"
                + "behavior f : (x: Int) -> Int\nlet f (x) = {\n    let t = (x, x)\n");
        for (int i = 0; i < statements; i++) {
            sb.append("    let (a").append(i).append(", b").append(i).append(") = t\n");
        }
        return sb.append("    x\n}\n").toString();
    }

    /** A 255-argument helper, applied where it is spliced: the widest expansion a definition may
     *  hold, under what nesting is left for it. */
    private static String widestExpansion(int nesting) {
        StringBuilder sb = new StringBuilder("module m exposing (f)\n\nlet h (");
        for (int i = 0; i < 255; i++) {
            sb.append(i == 0 ? "" : ", ").append("p").append(i).append(": Int");
        }
        sb.append(") = p0\n\nbehavior f : (x: Int) -> Int\nlet f (x) = h(");
        for (int i = 0; i < 255; i++) {
            sb.append(i == 0 ? "" : ", ").append("x");
        }
        return sb.append(")").append(" + 1".repeat(nesting)).append("\n").toString();
    }

    /** A block of guards: a step that binds nothing, and the only statement kind that does not. */
    private static String guards(int statements) {
        // The condition is a name, so what each guard holds is one level and the steps are what the
        // block costs. A written-out condition would be counted too, from where its guard stands,
        // which is the algebra working rather than the fixture being awkward.
        StringBuilder sb = new StringBuilder("module m exposing (f)\n\n"
                + "behavior f : (b: Bool) -> Int\nlet f (b) = {\n");
        for (int i = 0; i < statements; i++) {
            sb.append("    guard b else 0\n");
        }
        return sb.append("    1\n}\n").toString();
    }

    /** Guards, destructurings and a deep value in one block: every statement kind at once. */
    private static String everyStatementKind() {
        StringBuilder sb = new StringBuilder("module m exposing (f)\n\n"
                + "behavior f : (x: Int) -> Int\nlet f (x) = {\n    let t = (x, x)\n");
        for (int i = 0; i < 60; i++) {
            sb.append("    guard x > ").append(i).append(" else 0\n");
            sb.append("    let (a").append(i).append(", b").append(i).append(") = t\n");
        }
        return sb.append("    x").append(" + 1".repeat(50)).append("\n}\n").toString();
    }

    /** A block of statements over a chain of values: two producers in one definition. */
    private static String blockOverAChain() {
        StringBuilder sb = new StringBuilder("module m exposing (f)\n\nlet v0 = 1\n");
        for (int i = 1; i <= 188; i++) {
            sb.append("let v").append(i).append(" = v").append(i - 1).append(" + 1\n");
        }
        sb.append("\nbehavior f : (x: Int) -> Int\nlet f (x) = {\n    let a0 = x\n");
        for (int i = 1; i < 128; i++) {
            sb.append("    let a").append(i).append(" = a").append(i - 1).append("\n");
        }
        return sb.append("    a127 + v188\n}\n").toString();
    }

    /**
     * The bound accepts what is inside it and refuses what is one past, counted the way the source
     * says rather than the way anything was folded.
     *
     * <p>Asked with guards, which take a step each and bind nothing: what the fold leaves behind is
     * an {@code if} per guard, and what the source says is a step per guard, and the two are the
     * same count for reasons this holds one at a time. A block one step over says how many steps it
     * takes, not how many names it binds, because it binds none.
     */
    @Test
    void aBlockIsAcceptedToTheBoundAndRefusedOneStepPast() {
        // A guard is a step, and the result stands after all of them — so a block of n guards costs
        // n and then the result, and the last one that fits leaves the result on the bound.
        assertDoesNotThrow(() -> Compiler.compiled(guards(StructuralCost.MAX - 1), "m"));

        // One more, and the block says so before it is folded — in steps, because a guard binds
        // nothing and this block binds no names at all.
        CompileException steps = assertThrows(CompileException.class,
                () -> Compiler.compiled(guards(StructuralCost.MAX), "m"));
        assertEquals("E2107", steps.code(), steps.getMessage());
        assertTrue(steps.getMessage().contains((StructuralCost.MAX + 1) + " structural steps"),
                steps.getMessage());
        assertFalse(steps.getMessage().contains("binds " + (StructuralCost.MAX + 1)),
                "a block of guards binds no names, and this counts steps: " + steps.getMessage());
    }

    /**
     * A block named as a value and substituted somewhere else is counted the same on both sides of
     * the substitution.
     *
     * <p>Two things count a block: the pass that builds it, from the statements the source wrote,
     * and the pass that substitutes it, from what building it left behind. They have to agree, or a
     * definition is inside the bound where it is written and past it where it is named — and the
     * side that spoke would be whichever pass looked, which is what this bound is not to depend on.
     *
     * <p>The block here holds what it holds at its first statement, which is where the two ways of
     * counting part most: from the source that is no steps and then the payload, and from the tree
     * it is the binding and then the payload.
     */
    @Test
    void aBlockCostsTheSameWhereItIsWrittenAndWhereItIsSubstituted() {
        assertDoesNotThrow(() -> Compiler.compiled(aValueHoldingABlock(317), "m"),
                "a value whose block is inside the bound is substitutable");

        CompileException past = assertThrows(CompileException.class,
                () -> Compiler.compiled(aValueHoldingABlock(318), "m"));

        assertEquals("E2107", past.code(), past.getMessage());
        assertTrue(past.getMessage().contains("Substituting"), past.getMessage());
    }

    /**
     * A value whose body is a block, holding a chain of {@code names} values at its first
     * statement, named by a behavior so that substituting it is what the second count is of.
     *
     * <p>The chain is what makes the block expensive. Written nesting cannot: the parser bounds it
     * at a depth far under this one, so a block that holds a lot holds it through names.
     */
    private static String aValueHoldingABlock(int names) {
        StringBuilder sb = new StringBuilder("module m exposing (f)\n\nlet v0 = 1\n");
        for (int i = 1; i <= names; i++) {
            sb.append("let v").append(i).append(" = v").append(i - 1).append(" + 1\n");
        }
        sb.append("\nlet held = {\n    let a = v").append(names).append("\n    a\n}\n\n");
        return sb.append("behavior f : (x: Int) -> Int\nlet f (x) = x + held\n").toString();
    }

    /**
     * Blocks written inside blocks are refused by the count, not by running out.
     *
     * <p>Each of these is well under the bound on its own, and folding them descends once per step
     * of every one of them at once. Counted only where each block starts, they all pass and the
     * fold goes as deep as they come to together — which on the supported stack is deep enough to
     * give out, so what the author would be told is that the compiler ran out rather than what
     * their definition says.
     */
    @Test
    void blocksInsideBlocksAreCountedBeforeTheyAreFolded() {
        for (int nesting : new int[]{5, 15, 25, 30}) {
            CompileException said = assertThrows(CompileException.class,
                    () -> Compiler.compiled(blocksInsideBlocks(nesting, 319), "m"),
                    nesting + " blocks of 319 steps is past the bound");

            assertEquals("E2107", said.code(),
                    nesting + " blocks deep: " + said.getMessage());
        }
    }

    /**
     * The same, with something ordinary written around each block.
     *
     * <p>A block handed to a call or put in a tuple is a block the fold still descends. Counted
     * only where a block is a statement's value, this walks past — and what is written around it
     * costs the source nesting the parser bounds, so a shape like this is what a bound on blocks
     * alone would let build itself before saying anything.
     */
    @Test
    void aBlockWrappedInSomethingOrdinaryIsCountedToo() {
        for (int nesting : new int[]{5, 10, 15}) {
            CompileException said = assertThrows(CompileException.class,
                    () -> Compiler.compiled(wrappedBlocksInsideBlocks(nesting, 319), "m"),
                    nesting + " wrapped blocks of 319 steps is past the bound");

            assertEquals("E2107", said.code(), said.getMessage());
            assertTrue(said.getMessage().contains("structural steps"),
                    "the blocks are counted together: " + said.getMessage());
        }
    }

    /** A block holding nothing but another block: there is no statement of its own to report at. */
    @Test
    void aBlockOfNothingButAnotherBlockIsReportedAtWhatItHolds() {
        StringBuilder sb = new StringBuilder("module m exposing (f)\n\n"
                + "behavior f : (b: Bool) -> Int\nlet f (b) = {\n    {\n");
        for (int i = 0; i <= StructuralCost.MAX; i++) {
            sb.append("        guard b else 0\n");
        }
        String source = sb.append("        1\n    }\n}\n").toString();

        CompileException said = assertThrows(CompileException.class,
                () -> Compiler.compiled(source, "m"));

        assertEquals("E2107", said.code(), said.getMessage());
    }

    private static String wrappedBlocksInsideBlocks(int nesting, int stepsEach) {
        return "module m exposing (f)\n\nbehavior f : (x: Int) -> Int\nlet f (x) = "
                + oneWrapped(nesting, stepsEach, new int[]{0}) + "\n";
    }

    private static String oneWrapped(int nesting, int stepsEach, int[] named) {
        if (nesting == 0) {
            return "x";
        }
        StringBuilder sb = new StringBuilder("{\n");
        for (int i = 0; i < stepsEach; i++) {
            sb.append("    let a").append(named[0]++).append(" = x\n");
        }
        sb.append("    let held").append(nesting).append(" = (")
          .append(oneWrapped(nesting - 1, stepsEach, named)).append(") + 1\n");
        return sb.append("    held").append(nesting).append("\n}").toString();
    }

    /** {@code nesting} blocks of {@code stepsEach} statements, each written in the value of a
     *  statement of the one outside it. */
    private static String blocksInsideBlocks(int nesting, int stepsEach) {
        return "module m exposing (f)\n\nbehavior f : (x: Int) -> Int\nlet f (x) = "
                + oneOf(nesting, stepsEach, new int[]{0}) + "\n";
    }

    private static String oneOf(int nesting, int stepsEach, int[] named) {
        if (nesting == 0) {
            return "x";
        }
        StringBuilder sb = new StringBuilder("{\n");
        for (int i = 0; i < stepsEach; i++) {
            sb.append("    let a").append(named[0]++).append(" = x\n");
        }
        sb.append("    let held").append(nesting).append(" = ")
          .append(oneOf(nesting - 1, stepsEach, named)).append("\n");
        return sb.append("    held").append(nesting).append("\n}").toString();
    }

    @Test
    void whatIsBuiltFromASourceAtTheBoundStaysWithinReachOfTheWalks() {
        List<String> tooDeep = new ArrayList<>();
        record Case(String what, String source) {}
        List<Case> cases = List.of(
                new Case("a block at the bound", block(StructuralCost.MAX)),
                new Case("a chain of values at the bound", valueChain(StructuralCost.MAX, 1)),
                new Case("a chain of deep bodies", valueChain(StructuralCost.MAX, 60)),
                new Case("a block over a chain", blockOverAChain()),
                new Case("a record taken apart in a parameter", recordPattern(200)),
                new Case("a block of destructurings", destructuringBlock(100)),
                new Case("the widest expansion, under nesting", widestExpansion(50)),
                new Case("a block of guards", guards(300)),
                new Case("every statement kind at once", everyStatementKind()));

        for (Case one : cases) {
            Compilation compilation = Compiler.compiled(one.source(), "m");
            for (String module : compilation.modules()) {
                for (String behavior : compilation.declaredBehaviors(module)) {
                    say(tooDeep, one.what(), behavior, "the Ast it expanded",
                            depthOf(compilation.db()
                                    .ask(new Bodies.LoweredBody(module, behavior)).value()));
                    say(tooDeep, one.what(), behavior, "the Core it elaborated",
                            Depth.of(compilation.db()
                                    .ask(new Bodies.CheckedBehavior(module, behavior)).value()));
                }
            }
        }

        assertTrue(tooDeep.isEmpty(), "a source within the bound built deeper than "
                + (StructuralCost.MAX + SLACK) + ":\n  " + String.join("\n  ", tooDeep));
    }

    private static void say(List<String> tooDeep, String what, String behavior, String which,
                            int depth) {
        if (depth > StructuralCost.MAX + SLACK) {
            tooDeep.add(what + ", `" + behavior + "`: " + which + " is " + depth + " deep");
        }
    }

    /** The longest way down a written body, counted the way {@link Depth} counts a {@code Core}. */
    private static int depthOf(Ast.FnDef fn) {
        if (fn == null || !(fn.body() instanceof Ast.FnBody.Written written)) {
            return 0;
        }
        List<Ast.Expr> nodes = new ArrayList<>();
        List<Integer> above = new ArrayList<>();
        nodes.add(written.expr());
        above.add(0);
        int most = 0;
        while (!nodes.isEmpty()) {
            Ast.Expr node = nodes.remove(nodes.size() - 1);
            int here = above.remove(above.size() - 1) + 1;
            most = Math.max(most, here);
            Ast.forEachChild(node, child -> {
                if (child != null) {
                    nodes.add(child);
                    above.add(here);
                }
            });
        }
        return most;
    }
}
