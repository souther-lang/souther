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
 * representation must not be what decides whether the boundary admits it.
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
    void theReservedNameIsRefusedWhicheverWayItArrives() {
        assertNull(CrossingNominal.admitted(TypeSymbol.primitive("Raw"), null));
    }

    @Test
    void theScalarsTheBoundaryWritesAreNotRefused() {
        for (Type.Prim prim : Type.Prim.values()) {
            if (prim == Type.Prim.RAW) {
                continue;
            }
            assertNotNull(LeafScalar.of(prim), prim.toString());
            assertNotNull(CrossingNominal.admitted(TypeSymbol.primitive(Type.show(prim)), null),
                    prim.toString());
        }
    }
}
