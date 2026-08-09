package souther.compiler.core;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.ast.Ast;
import souther.compiler.ast.StructuralCost;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;

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
class AnAcceptedSourceBuildsNoDeeperThanTheBoundTest {

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
                new Case("the widest expansion, under nesting", widestExpansion(50)));

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
