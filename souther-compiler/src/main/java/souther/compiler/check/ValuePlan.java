package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.BinOp;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.SequencedMap;
import java.util.function.Predicate;

/**
 * Which values a region demands where it stands, as opposed to inside a region it opens.
 *
 * <p>A region is somewhere entered on some paths and not others — a branch, an arm, the right of a
 * short-circuit, the body of a block, the element a comprehension writes per item. What it demands
 * is what it names without crossing into one of those, and that is where a value is built: at the
 * head of the region, once, so it is evaluated exactly where some reference to it would have been.
 * Asked of the body of a value the same way, it says which values the value's own build takes in
 * the region that builds it.
 *
 * <p>Only the decision. What is done with what is demanded — a value handed to a method, a copy of
 * its body bound in the region — is the reader's, and this knows of neither.
 *
 * @param rootDemands the values the region names at its own level, first reference of each, by the
 *                    name each is reached by, and those every way out of a fork names
 */
record ValuePlan(SequencedMap<String, Hir.Var.Denoting> rootDemands) {

    /**
     * The plan of {@code region}.
     *
     * @param aValue whether a reference is to a value that is built where it is demanded, and not
     *               to anything else a name can stand for
     */
    static ValuePlan of(Hir.Expr region, Predicate<Hir.Var.Denoting> aValue) {
        SequencedMap<String, Hir.Var.Denoting> out = new LinkedHashMap<>();
        demanded(region, aValue, out);
        return new ValuePlan(out);
    }

    private static void demanded(Hir.Expr e, Predicate<Hir.Var.Denoting> aValue,
                                 SequencedMap<String, Hir.Var.Denoting> out) {
        if (e == null) {
            return;
        }
        switch (e) {
            case Hir.Var.Denoting named when aValue.test(named) ->
                    out.putIfAbsent(named.reaches(), named);
            case Hir.If iff -> {
                demanded(iff.cond(), aValue, out);
                onEveryWayOut(List.of(iff.then(), iff.els()), aValue, out);
            }
            case Hir.IfConstructed ic -> {
                demanded(ic.construct(), aValue, out);
                List<Hir.Expr> ways = new ArrayList<>();
                ways.add(ic.then());
                for (Hir.ElseArm arm : ic.els()) {
                    ways.add(arm.body());
                }
                onEveryWayOut(ways, aValue, out);
            }
            case Hir.Match m -> {
                demanded(m.scrutinee(), aValue, out);
                List<Hir.Expr> ways = new ArrayList<>();
                for (Hir.Case each : m.cases()) {
                    ways.add(each.body());
                }
                onEveryWayOut(ways, aValue, out);
            }
            case Hir.Binary b when isShortCircuit(b) -> demanded(b.left(), aValue, out);
            case Hir.Block _ -> { }
            case Hir.ListComp _ -> { }
            default -> Hir.forEachChild(e, child -> demanded(child, aValue, out));
        }
    }

    /**
     * The values every one of {@code ways} names, added to what the region around them demands.
     *
     * <p>A fork's arms are ways out of one place: whichever is taken, one of them is. So a value
     * every arm names is named on every path through here, and binding it around the fork
     * evaluates it exactly where some reference to it is evaluated — which is the whole of what
     * keeps the region rule from moving work onto a path that had none.
     *
     * <p>Only the forks that are ways out. The right of a short-circuit is reached for some of what
     * reaches the left, a block's body for each application of it and a comprehension's element for
     * each item, and none of those is a way the code has to go.
     *
     * <p>Which says nothing about how often the fork runs, only about whether it does. A value
     * bound here and read in one arm is built once whichever arm runs, where arm-local bindings
     * would each build it — one materialisation per region, told of a place that is one region.
     */
    private static void onEveryWayOut(List<Hir.Expr> ways, Predicate<Hir.Var.Denoting> aValue,
                                      SequencedMap<String, Hir.Var.Denoting> out) {
        SequencedMap<String, Hir.Var.Denoting> shared = null;
        for (Hir.Expr way : ways) {
            SequencedMap<String, Hir.Var.Denoting> named = new LinkedHashMap<>();
            demanded(way, aValue, named);
            if (shared == null) {
                shared = named;
            } else {
                shared.keySet().retainAll(named.keySet());
            }
            if (shared.isEmpty()) {
                return;
            }
        }
        if (shared != null) {
            shared.forEach(out::putIfAbsent);
        }
    }

    /** Whether what stands on the right of this is reached only for some of what reaches the
     *  left. */
    static boolean isShortCircuit(Hir.Binary b) {
        return b.op() == BinOp.AND || b.op() == BinOp.OR;
    }
}
