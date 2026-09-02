package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.frontend.CstFrontend;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * The form a declaration is written in below the settling does not depend on whether a
 * representation could be derived for it.
 *
 * <p>Two things happen to a declaration at the derived stage, and they are told apart here: the
 * newtype constructions in what it says about itself are written as the constructions they denote,
 * and a product's decoder and encoder are read off its shape. The second can fail — a field whose
 * type nobody could name has no representation — and the first cannot fail for that reason.
 *
 * <p>What rests on it is the surface a best-effort reading of a module is given. A module holding
 * one declaration that could not be derived is still read for what its other definitions say, and
 * the declaration that could not be derived is on that surface in the form every reader below the
 * settling expects. Were the two written apart, the surface would carry an earlier spelling of one
 * declaration beside the settled spelling of the rest, and nothing in the tree would say which was
 * which.
 */
class ADeclarationIsWrittenOneWayWhetherOrNotItsRepresentationCameOutTest {

    /** A declaration whose clause writes a construction, beside one whose field names nothing. */
    private static final String MODULE = """
            module m exposing ( Wrapped, Amount )

            data Wrapped = Int
            data Amount = Int
                invariant isOk(value)

            data Broken = { value: Nowhere }

            let isOk (n: Int) : Bool = Wrapped(n) == Wrapped(0)
            """;

    private final ResolvedSymbols scope = symbols();
    private final InvariantSettled settled = settle();

    @Test
    void aDeclarationThatDerivedIsTheNormalisedDeclaration() {
        InvariantSettled.Def amount = defNamed("Amount");

        Derived.Def derived = Derived.Def.derive(amount, scope);

        assertNotNull(derived, "`Amount` has a representation to derive");
        assertEquals(Derived.normalized(amount, scope), derived.declared(),
                "what the derived declaration holds is what the normalisation answered with");
    }

    /**
     * And one that did not derive is normalised all the same.
     *
     * <p>The two halves measured apart: the representation is absent and the constructions in the
     * clauses are still written as constructions. A reader given the settled spelling instead would
     * be given a declaration written one rung up from the ones beside it.
     */
    @Test
    void aDeclarationThatDidNotDeriveIsStillNormalised() {
        InvariantSettled.Def broken = defNamed("Broken");

        assertNull(Derived.Def.derive(broken, scope),
                "nothing could be derived for a field whose type names nothing");
        assertNotNull(Derived.normalized(broken, scope),
                "and the declaration is still written in the form the stage below reads");
    }

    /** The normalisation is one operation and not two readings that happen to agree today. */
    @Test
    void everyDeclarationIsNormalisedByTheOneOperation() {
        for (InvariantSettled.Def def : settled.defs()) {
            Hir.Def normalised = Derived.normalized(def, scope);
            Derived.Def derived = Derived.Def.derive(def, scope);
            if (derived != null) {
                assertEquals(normalised, derived.declared(),
                        "`" + def.name() + "` is written the same way either way");
            }
        }
    }

    /** A declaration with nothing to rewrite comes back as the node it already was, which is what
     *  says the operation is a rewrite and not a copy. */
    @Test
    void aDeclarationWithNothingToRewriteIsTheDeclarationItWas() {
        InvariantSettled.Def wrapped = defNamed("Wrapped");

        assertSame(wrapped.def(), Derived.normalized(wrapped, scope));
    }

    private InvariantSettled.Def defNamed(String name) {
        for (InvariantSettled.Def def : settled.defs()) {
            if (def.name().equals(name)) {
                return def;
            }
        }
        throw new AssertionError("the module declares `" + name + "`");
    }

    private static ResolvedSymbols symbols() {
        return TypeChecker.symbols(resolved(), DefaultStdlib.get());
    }

    private InvariantSettled settle() {
        return InvariantSettled.settle(
                Expandable.check(resolved(), Map.of(), DefaultStdlib.get()), scope, Map.of());
    }

    private static Hir.Module resolved() {
        Ast.Module parsed = CstFrontend.parse(MODULE);
        return Resolve.resolving(parsed, SyntaxSymbols.of(parsed, DefaultStdlib.get())).module();
    }
}
