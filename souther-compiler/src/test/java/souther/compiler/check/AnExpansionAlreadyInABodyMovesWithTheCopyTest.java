package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Ast;
import souther.compiler.ast.DefinitionName;
import souther.compiler.ast.Hir;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.types.BindingOwner;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A body that already holds an expansion is copied with that expansion, and it moves.
 *
 * <p>The other way a copy is made, and the one nothing else here reaches. A body whose calls are
 * still calls is copied and the calls in it are expanded afterwards, each under the copy it landed
 * in; a body whose calls were expanded before it was reached has nothing left to expand, so what
 * arrives in the copy is the expansion itself. Carried across as it stood, two copies of one body
 * would hold two expansions saying they wrote into one place, while the bindings each of them made
 * had gone to two.
 *
 * <p><b>Staged on purpose, because the shape does not arise from a source alone.</b> Expanding a
 * body in one go leaves nothing already expanded for a later copy to carry: the calls are met and
 * expanded where they stand. So the helper is expanded on its own first and put back as a
 * definition whose body is what that expansion left — which is what a pass that settles helpers one
 * at a time leaves for the one that reads them next.
 */
class AnExpansionAlreadyInABodyMovesWithTheCopyTest {

    private static final String MODULE = """
            module demo

            data X = Int

            let inner (n: Int) : Int = n + 1
            let middle (n: Int) : Int = inner(n)
            let top (m: Int) : Int = middle(m) + middle(m)

            behavior f : (x: X) -> X
            let f (x) = x
            """;

    @Test
    void anExpansionCarriedIntoTwoCopiesIsTwoExpansions() {
        Hir.Expr body = topOverAnExpandedMiddle();
        List<BindingOwner.Expansion> middles = applicationsOf(body, "middle");
        List<BindingOwner.Expansion> inners = applicationsOf(body, "inner");

        assertEquals(2, middles.size(), "the helper is written into the body twice");
        assertNotEquals(middles.get(0), middles.get(1),
                "and the two copies of it are two");
        assertEquals(2, inners.size(),
                "each copy carries the expansion its body already held");
        // Under the copy and not directly under it. The expansion was placed by a writing into the
        // helper's own body, and that writing is part of what it is written under — so what moved
        // is the whole chain, with the copy at the bottom of it.
        assertTrue(inners.stream()
                        .allMatch(each -> under(each).stream().anyMatch(middles::contains)),
                "and each of those belongs to the copy it was carried into: " + inners);
        assertNotEquals(inners.get(0), inners.get(1),
                "so the two are two, which is the whole of what moving it is for");
    }

    /**
     * And what each carried expansion says it wrote is where its bindings went.
     *
     * <p>The half that fails apart from the one above if the owner an expansion carries and the
     * owner its bindings are minted under are worked out in two places: both would move, and they
     * would move differently.
     */
    @Test
    void andEachOfThemOwnsTheBindingsItWrote() {
        List<String> astray = new ArrayList<>();
        eachExpansion(topOverAnExpandedMiddle(), ex -> ex.bound().forEach(bound -> {
            if (!ex.application().equals(bound.binder().id().owner())) {
                astray.add(bound.binder().name() + " of " + ex.callee()
                        + " belongs to " + bound.binder().id().owner()
                        + " and the expansion is " + ex.application());
            }
        }));

        assertEquals(List.of(), astray,
                "a copy of an expansion owns the bindings that copy wrote");
    }

    /** That the body under test holds what this is about: an expansion arriving already built. */
    @Test
    void andTheBodyUnderTestCarriesOneRatherThanBuildingIt() {
        assertEquals(List.of("inner"), calleesOf(expandedMiddle()),
                "the staged helper's body holds the expansion rather than the call");
    }

    /**
     * {@code top} expanded against a module whose {@code middle} has already been expanded.
     *
     * <p>Two inliners, because the staging is the point: the first reads the module as written and
     * expands one helper; the second reads a module where that helper's body is what the first one
     * left, so the only thing it can do with it is copy it.
     */
    private static Hir.Expr topOverAnExpandedMiddle() {
        Hir.Module resolved = resolved();
        Hir.FnDef middle = fnOf(resolved, "middle");
        List<Hir.FnDef> staged = new ArrayList<>();
        for (Hir.FnDef each : resolved.fns()) {
            staged.add(each == middle
                    ? middle.withBody(new Hir.FnBody.Written(expandedMiddle())) : each);
        }
        HelperInliner over = inlinerOver(resolved.withFns(staged));
        return over.inline(
                over.held().get(new DefinitionName("top")).definition().writtenBody(),
                over.bodyOf("top"));
    }

    /** {@code middle} expanded on its own, which is a body holding an expansion. */
    private static Hir.Expr expandedMiddle() {
        Hir.Module resolved = resolved();
        HelperInliner first = inlinerOver(resolved);
        return first.inline(fnOf(resolved, "middle").writtenBody(), first.bodyOf("middle"));
    }

    private static Hir.Module resolved() {
        Ast.Module parsed = CstFrontend.parse(MODULE);
        return Resolve.module(parsed, SyntaxSymbols.of(parsed, DefaultStdlib.get()));
    }

    private static HelperInliner inlinerOver(Hir.Module module) {
        return HelperInliner.forModule(module, DefaultStdlib.get());
    }

    private static Hir.FnDef fnOf(Hir.Module module, String name) {
        return module.fns().stream().filter(each -> each.name().equals(name)).findFirst()
                .orElseThrow(() -> new AssertionError("the model under test declares " + name));
    }

    /** Every application of {@code helper} in {@code body}, in the order the tree holds them. */
    private static List<BindingOwner.Expansion> applicationsOf(Hir.Expr body, String helper) {
        List<BindingOwner.Expansion> out = new ArrayList<>();
        eachExpansion(body, ex -> {
            if (ex.callee().name().equals(helper)
                    && ex.application() instanceof BindingOwner.Expansion at) {
                out.add(at);
            }
        });
        return out;
    }

    /** What every expansion in {@code body} is an expansion of. */
    private static List<String> calleesOf(Hir.Expr body) {
        List<String> out = new ArrayList<>();
        eachExpansion(body, ex -> out.add(ex.callee().name()));
        return out;
    }

    /** Everything {@code owner} is written under, innermost first. */
    private static List<BindingOwner> under(BindingOwner owner) {
        List<BindingOwner> out = new ArrayList<>();
        BindingOwner at = owner;
        while (true) {
            BindingOwner next = switch (at) {
                case BindingOwner.Expansion it -> it.within();
                case BindingOwner.Synthesized it -> it.within();
                default -> null;
            };
            if (next == null) {
                return out;
            }
            out.add(next);
            at = next;
        }
    }

    private static void eachExpansion(Hir.Expr e, java.util.function.Consumer<Hir.Expansion> at) {
        if (e instanceof Hir.Expansion ex) {
            at.accept(ex);
        }
        Hir.forEachChild(e, child -> eachExpansion(child, at));
    }
}
