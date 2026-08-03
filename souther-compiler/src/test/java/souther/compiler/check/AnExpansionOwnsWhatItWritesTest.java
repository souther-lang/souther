package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every binding an expansion writes belongs to that expansion.
 *
 * <p>Expanding a call writes several bindings: one per argument, one for a lambda given to a function
 * parameter, one carrying the declared return, and one for every binding copied out of the callee's
 * body. They are one call's, and a reader that has to answer something about the call — which
 * signature they came from, what one variable of it stands for — can only do that if it can tell
 * which of them are the same call's. Owning them is what says so; before this, only the copied body's
 * were owned by the expansion and the rest belonged to the pass.
 */
class AnExpansionOwnsWhatItWritesTest {

    private static Ast.Module resolved(String source) {
        Ast.Module parsed = CstFrontend.parse(source);
        return Resolve.module(parsed, Symbols.of(parsed));
    }

    /** Every binding in {@code e}, in the order they are written. */
    private static List<Ast.Binder> binders(Ast.Expr e) {
        List<Ast.Binder> out = new ArrayList<>();
        collect(e, out);
        return out;
    }

    private static void collect(Ast.Expr e, List<Ast.Binder> out) {
        if (e instanceof Ast.LetIn li) {
            out.add(li.binder());
        }
        if (e instanceof Ast.Block b) {
            out.addAll(b.params());
        }
        TypeChecker.forEachChild(e, c -> collect(c, out));
    }

    /** The expansion each of {@code binders} belongs to, or null where it belongs to something else. */
    private static Set<BindingOwner.Expansion> expansionsOf(List<Ast.Binder> binders) {
        Set<BindingOwner.Expansion> out = new LinkedHashSet<>();
        for (Ast.Binder b : binders) {
            if (b.id().owner() instanceof BindingOwner.Expansion x) {
                out.add(x);
            }
        }
        return out;
    }

    private static Ast.Expr expanded(String defs, String of) {
        Ast.Module m = resolved("""
                module demo
                data X = Int
                behavior f : (x: X) -> X
                %s
                let f (x) = x
                """.formatted(defs));
        HelperInliner inliner = HelperInliner.forModule(m);
        return inliner.inline(inliner.helpers().get(of).written(), inliner.bodyOf(of));
    }

    @Test
    void everyBindingOneExpansionWritesIsThatExpansionsOwn() {
        // `taxed` takes two arguments and its body binds one of its own, so the expansion writes
        // three bindings. All three are this call's.
        Ast.Expr body = expanded("""
                let taxed (n: Int, rate: Int) = {
                    let scaled = n * rate
                    scaled / 100
                }
                let go (m: Int) = taxed(m, 11)""", "go");
        List<Ast.Binder> written = binders(body);
        assertFalse(written.isEmpty(), "the expansion writes bindings");
        assertEquals(1, expansionsOf(written).size(), "they are one call's");
        for (Ast.Binder b : written) {
            assertTrue(b.id().owner() instanceof BindingOwner.Expansion,
                    "`" + b.name() + "` belongs to " + b.id().owner());
        }
    }

    @Test
    void twoCallsOfOneHelperAreTwoExpansions() {
        Ast.Expr body = expanded("""
                let twice (n: Int) = n * 2
                let go (m: Int) = twice(m) + twice(m + 1)""", "go");
        assertEquals(2, expansionsOf(binders(body)).size(), "two calls, two expansions");
    }

    @Test
    void anExpansionInsideAnExpansionIsAnotherExpansion() {
        Ast.Expr body = expanded("""
                let inner (n: Int) = n * 2
                let outer (n: Int) = inner(n) + 1
                let go (m: Int) = outer(m)""", "go");
        assertEquals(2, expansionsOf(binders(body)).size(), "the inner call is its own expansion");
    }

    /** Two bindings of one expansion are two bindings: one minter, so the ordinals do not repeat. */
    @Test
    void noTwoBindingsOfOneExpansionAreTheSameBinding() {
        Ast.Expr body = expanded("""
                let taxed (n: Int, rate: Int) = {
                    let scaled = n * rate
                    scaled / 100
                }
                let go (m: Int) = taxed(m, 11) + taxed(m, 12)""", "go");
        List<Ast.Binder> written = binders(body);
        Set<BindingId> distinct = new LinkedHashSet<>();
        for (Ast.Binder b : written) {
            assertTrue(distinct.add(b.id()), "`" + b.name() + "` repeats " + b.id());
        }
        assertEquals(written.size(), distinct.size());
    }
}
