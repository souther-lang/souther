package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.TypeName;

import org.junit.jupiter.api.Test;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A body expanded after one that was refused is expanded as if nothing had been refused.
 *
 * <p>Expanding is not all-or-nothing to the caller. {@code HelperParams} settles the helpers of a
 * module one at a time and keeps going past one it cannot read, and {@code TypeChecker} records a
 * refusal and checks the next unit, so a module reports more than one mistake. Both hand the same
 * inliner the next body. What the refused expansion had written down by the time it was refused is
 * therefore still there when the next one starts.
 *
 * <p>Nothing states that, and the way it would be found is not a failure but a difference: a body
 * expanded into a tree that is subtly not the one it would have been. So the two are compared —
 * one expansion after a refusal, one on its own — and they have to be equal.
 */
class AnExpansionAfterARefusalIsWhatItWouldHaveBeenTest {

    /**
     * {@code applyTwice} hands its function parameter two arguments where the lambda given to it
     * takes one, so expanding {@code wrong} is refused — after the lambda has been registered under
     * the binding the expansion made for it, and before the expansion has finished with it.
     */
    private static final String MODULE = """
            module demo

            data X = Int

            let applyTwice (f: (Int) -> Int, n: Int) : Int = f(n, n)
            let doubled (n: Int) : Int = n * 2
            let wrong (m: Int) : Int = applyTwice((x) -> x + 1, m)
            let right (m: Int) : Int = doubled(m) + 1

            behavior f : (x: X) -> X
            let f (x) = x
            """;

    private static HelperInliner inliner() {
        Ast.Module parsed = CstFrontend.parse(MODULE);
        return HelperInliner.forModule(Resolve.module(parsed, SyntaxSymbols.of(parsed)));
    }

    private static Hir.Expr expand(HelperInliner inliner, String helper) {
        return inliner.inline(inliner.held().get(helper).writtenBody(), inliner.bodyOf(helper));
    }

    @Test
    void theOneWrittenWrongIsRefused() {
        assertThrows(CompileException.class, () -> expand(inliner(), "wrong"));
    }

    @Test
    void theNextBodyIsExpandedAsThoughTheRefusalHadNotHappened() {
        HelperInliner afterARefusal = inliner();
        assertThrows(CompileException.class, () -> expand(afterARefusal, "wrong"));
        Hir.Expr next = expand(afterARefusal, "right");

        Hir.Expr onItsOwn = expand(inliner(), "right");

        assertEquals(onItsOwn, next,
                "what the refused expansion left behind changed what came after it");
    }

    /**
     * The other half of the same rule. A body can be written into more than once — one writing per
     * clause of a declaration's invariant, one per argument of a helper being checked — and the two
     * writings are still two, so what they write are different bindings.
     */
    @Test
    void twoWritingsIntoOneBodyDoNotWriteTheSameBinding() {
        HelperInliner inliner = inliner();
        BindingOwner body = new BindingOwner.OfData(new TypeName("demo", "X"));
        Hir.Expr clause = inliner.held().get("right").writtenBody();

        Set<BindingId> first = bindingsOf(inliner.inline(clause, body));
        Set<BindingId> second = bindingsOf(inliner.inline(clause, body));

        assertFalse(first.isEmpty(), "the expansion writes bindings");
        assertTrue(Collections.disjoint(first, second),
                "the second writing wrote the first one's bindings over again: " + first);
    }

    /** Every binding written inside {@code e}. */
    private static Set<BindingId> bindingsOf(Hir.Expr e) {
        Set<BindingId> out = new LinkedHashSet<>();
        collect(e, out);
        return out;
    }

    private static void collect(Hir.Expr e, Set<BindingId> out) {
        if (e instanceof Hir.LetIn li) {
            out.add(li.binder().id());
        }
        if (e instanceof Hir.Expansion ex) {
            ex.bound().forEach(b -> out.add(b.binder().id()));
        }
        Hir.forEachChild(e, c -> collect(c, out));
    }
}
