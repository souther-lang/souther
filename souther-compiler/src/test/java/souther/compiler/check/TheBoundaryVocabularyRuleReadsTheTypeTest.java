package souther.compiler.check;

import souther.compiler.types.LeafScalar;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * The rule is asked of the type, not of the name a source spelling happened to resolve to. Written
 * `Raw` currently denotes a reference rather than the primitive, and asking the reference is what
 * refuses it in a compiled module — but the primitive is the same type, so correcting that
 * representation must not be what decides whether the boundary admits it. Both readings refuse it:
 * no name of the language's namespace is a model's declaration, and `Raw` is no scalar the boundary
 * writes.
 *
 * <p>A primitive is classified without asking the model anything, which is why these pass no symbols:
 * needing them would mean the answer could depend on what a module declared, and it cannot.
 */
class TheBoundaryVocabularyRuleReadsTheTypeTest {

    @Test
    void theReservedPrimitiveIsNoScalarTheBoundaryWrites() {
        assertNull(LeafScalar.of(Type.Prim.RAW));
    }

    @Test
    void theScalarsTheBoundaryWritesAreNamedByALeaf() {
        for (Type.Prim prim : Type.Prim.values()) {
            if (prim == Type.Prim.RAW) {
                continue;
            }
            assertNotNull(LeafScalar.of(prim), prim.toString());
        }
    }

    /**
     * No name of the language's own namespace is a declaration to admit — not the ones standing for a
     * scalar, and not the ones standing for nothing.
     *
     * <p>Held here rather than through a module that names one, because no source reaches it: `Some`
     * and `None` in a union are refused as members before a signature is built (E1613), and the
     * namespace takes any spelling at all. What the witness says is that a model declared the name,
     * and one minted for `Int` or for `Some` is that sentence being false while every reader below
     * goes on acting as though it were true. Where a scalar's name legitimately arrives — a union's
     * member — the position tells the two apart and holds each to its own rule.
     */
    @Test
    void noNameOfTheLanguagesNamespaceIsAModelsDeclaration() {
        assertNull(CrossingNominal.admitted(TypeSymbol.primitive("Raw"), null));
        assertNull(CrossingNominal.admitted(TypeSymbol.SOME, null));
        assertNull(CrossingNominal.admitted(TypeSymbol.NONE, null));
        assertNull(CrossingNominal.admitted(TypeSymbol.primitive("Anything"), null));
        for (Type.Prim prim : Type.Prim.values()) {
            assertNull(CrossingNominal.admitted(TypeSymbol.primitive(prim), null), prim.toString());
        }
    }
}
