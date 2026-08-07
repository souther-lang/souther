package souther.compiler.check;

import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
    void theReservedPrimitiveIsRefusedAsItself() {
        assertEquals("Raw", TypeOps.foreignNameInBoundaryShape(Type.RAW, null).name());
    }

    @Test
    void theReservedPrimitiveIsRefusedAtDepth() {
        assertEquals("Raw",
                TypeOps.foreignNameInBoundaryShape(Type.list(Type.RAW), null).name());
        assertEquals("Raw",
                TypeOps.foreignNameInBoundaryShape(Type.map(Type.STRING, Type.RAW), null).name());
    }

    @Test
    void theScalarsTheBoundaryWritesAreNotRefused() {
        for (Type.Prim prim : Type.Prim.values()) {
            if (prim == Type.Prim.RAW) {
                continue;
            }
            assertNull(TypeOps.foreignNameInBoundaryShape(prim, null), prim.toString());
        }
    }
}
