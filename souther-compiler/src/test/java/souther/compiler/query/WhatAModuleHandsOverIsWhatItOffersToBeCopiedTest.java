package souther.compiler.query;

import souther.compiler.ast.Hir;
import souther.compiler.check.CarriedDefinitions;
import souther.compiler.copied.CopyTarget;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every definition a module hands to other modules' readers is one it offers to be copied, and it
 * offers no other.
 *
 * <p>What a module hands over is one answer ({@link CarriedDefinitions}) read by what its jar carries
 * and by what it offers. A definition handed over and not offered is one a reader can copy with
 * nothing to hold the copy to — a helper a module keeps to itself and calls from its invariant, say,
 * which a type including the invariant reads. Asked of the offer directly, since a reader that
 * reaches such a helper is not what decides whether the module offers it.
 */
class WhatAModuleHandsOverIsWhatItOffersToBeCopiedTest {

    private static final String LIB = """
            module lib.v exposing ( Base, Chain, capped, limit )
            data Chain = { k: Int, next: Chain? }
            let valid (c: Chain): Bool = match c.next with
                | Some rest -> c.k >= 0 && valid(rest)
                | None -> c.k >= 0
            let positive (n: Int) = n > 0
            data Base = { chain: Chain, n: Int }
                invariant ok = valid(chain) && positive(n)
            let unused (n: Int) = n
            let limit = 3
            let capped (n: Int) = if n > limit then limit else n
            """;

    @Test
    void whatIsHandedOverIsWhatIsOfferedAsAHelperOrAValue() {
        Compilation compilation = Compilation.ofSources(List.of(LIB), ModulePath.of(Map.of()));
        Hir.Module resolved = compilation.db().ask(new Names.Resolved("lib.v")).value();
        Hir.Module settled = compilation.db().ask(new Bodies.Settled("lib.v")).value();

        Set<String> handedOver = new TreeSet<>(
                CarriedDefinitions.of(resolved, settled.published()));
        Set<String> offered = new TreeSet<>();
        for (CopyTarget target : compilation.db().ask(new Copies.Provided("lib.v")).value()
                .provides().keySet()) {
            switch (target) {
                case CopyTarget.Helper(ValueName.Helper helper) -> offered.add(helper.name());
                case CopyTarget.Value(ValueName.Helper value) -> offered.add(value.name());
                case CopyTarget.Invariant _ -> { }
            }
        }

        assertEquals(Set.of("capped", "limit", "positive", "valid"), handedOver,
                "what the invariant calls and what is published, and not `unused`");
        assertEquals(handedOver, offered);
    }
}
