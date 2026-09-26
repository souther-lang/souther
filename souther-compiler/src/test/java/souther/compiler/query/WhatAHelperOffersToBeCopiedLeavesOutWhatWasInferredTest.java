package souther.compiler.query;

import souther.compiler.ast.Hir;
import souther.compiler.check.HelperInliner;
import souther.compiler.check.InliningPolicy;
import souther.compiler.copied.CopiedIdentity;
import souther.compiler.copied.CopyRecord;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a helper offers to be copied holds the types its author wrote and not the ones the checker
 * worked out: neither the type of a parameter its author left unwritten, nor the types an expansion
 * of another helper carries, which are that helper's signature instantiated at the call.
 *
 * <p>Both follow from what is held and from the rules the boundary revision stands for. Held here
 * as well, what a module offers would move with how the checker works a type out rather than with
 * what the module wrote, and a module off the path would offer, worked out again, something other
 * than what its classes record.
 *
 * <p>Asked of the closed definition with one worked-out type put in another's place, which no
 * source can write: a source that makes the checker work out another type is another source.
 */
class WhatAHelperOffersToBeCopiedLeavesOutWhatWasInferredTest {

    private static final String B = """
            module lib.b exposing ( has )
            let inner (ys, z) = List.contains(z, ys)
            let has (xs, y) = inner(xs, y)
            """;

    private static final Hir.RetType A_STRING =
            Hir.RetType.of(List.of(Hir.TypeRef.of(Type.Prim.STRING, null)), null);

    @Test
    void aParameterTypeTheCheckerWorkedOutIsNotPartOfTheOffer() {
        Hir.FnDef has = closed("has");
        assertTrue(has.params().stream()
                        .allMatch(p -> p.typeFrom() == Hir.ParameterTypeFrom.INFERRED),
                "the checker worked out what `has` takes");

        assertEquals(offered(has), offered(has.withParams(typed(has, Hir.ParameterTypeFrom.INFERRED))));
    }

    @Test
    void aParameterTypeTheAuthorWroteIs() {
        Hir.FnDef has = closed("has");

        assertNotEquals(offered(has), offered(has.withParams(typed(has, Hir.ParameterTypeFrom.WRITTEN))));
    }

    /** `has` is closed over `inner`, and the expansion of it carries what `inner`'s parameters were
     *  worked out as, instantiated at the call. */
    @Test
    void aTypeAnExpansionCarriesIsNotPartOfTheOffer() {
        Hir.FnDef has = closed("has");
        Hir.Expansion inner = assertInstanceOfExpansion(has.writtenBody());
        List<Hir.Bound> retyped = new ArrayList<>();
        inner.bound().forEach(b -> retyped.add(
                new Hir.Bound(b.binder(), A_STRING, b.value(), b.argument())));
        Hir.Expansion otherwise = new Hir.Expansion(inner.callee(), inner.application(), inner.at(),
                retyped, inner.given(), A_STRING, inner.body(), inner.pos(), inner.region());

        assertEquals(offered(has), offered(has.withBody(new Hir.FnBody.Written(otherwise))));
    }

    /** Each parameter of {@code fn} typed as a String, said to have come {@code from} there. */
    private static List<Hir.FnParam> typed(Hir.FnDef fn, Hir.ParameterTypeFrom from) {
        List<Hir.FnParam> out = new ArrayList<>();
        fn.params().forEach(p -> out.add(new Hir.FnParam(p.binder(), A_STRING, from)));
        return out;
    }

    private static Hir.Expansion assertInstanceOfExpansion(Hir.Expr body) {
        Hir.Expr at = body;
        while (at instanceof Hir.LetIn let) {
            at = let.body();
        }
        if (!(at instanceof Hir.Expansion expansion)) {
            throw new AssertionError("`has` is the expansion of `inner`, and it is " + at);
        }
        return expansion;
    }

    private static final Compilation COMPILED =
            Compilation.ofSources(List.of(B), ModulePath.of(Map.of()));

    /** {@code name} as `lib.b` hands it to a reader. */
    private static Hir.FnDef closed(String name) {
        Hir.Module settled = COMPILED.db().ask(new Bodies.Settled("lib.b")).value();
        Bodies.Expanding.Of against =
                COMPILED.db().ask(new Bodies.Expanding("lib.b", InliningPolicy.FULL)).value();
        Hir.FnDef declared = HelperInliner.helpersOf(settled).get(name);
        return Bodies.carriedClosure(settled, List.of(declared), against).get("lib.b." + name);
    }

    private static CopyRecord offered(Hir.FnDef closed) {
        Bodies.Expanding.Of against =
                COMPILED.db().ask(new Bodies.Expanding("lib.b", InliningPolicy.FULL)).value();
        return CopiedIdentity.helper(closed, new CopiedIdentity.Owner("lib.b",
                helper -> against.table().reached(new ReachName.Own(helper))));
    }
}
