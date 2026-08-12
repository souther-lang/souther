package souther.compiler.check;

import souther.compiler.types.LeafScalar;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

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
        assertFalse(TypeOps.declaredByAModel(TypeName.primitive("Raw"), null));
    }

    @Test
    void theScalarsTheBoundaryWritesAreNotRefused() {
        for (Type.Prim prim : Type.Prim.values()) {
            if (prim == Type.Prim.RAW) {
                continue;
            }
            assertNotNull(LeafScalar.of(prim), prim.toString());
            assertTrue(TypeOps.declaredByAModel(TypeName.primitive(Type.show(prim)), null),
                    prim.toString());
        }
    }
}
