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
                new Case("a block over a chain", blockOverAChain()));

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
