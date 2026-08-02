package souther.compiler.codegen;

import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The backend refuses a type that has no JVM carrier — the checker never lets one through, so
 * meeting one here is a compiler fault and says which type it met, not a cast failure.
 */
class JvmTypesTest {

    @Test
    void aTypeWithNoCarrierIsRefusedByName() {
        IllegalStateException never =
                assertThrows(IllegalStateException.class, () -> JvmTypes.jvmType(Type.NEVER, null));
        assertEquals("no JVM carrier for Never", never.getMessage());
        IllegalStateException erroneous =
                assertThrows(IllegalStateException.class,
                        () -> JvmTypes.jvmType(Type.ERRONEOUS, null));
        assertEquals("no JVM carrier for ?", erroneous.getMessage());
        IllegalStateException raw =
                assertThrows(IllegalStateException.class, () -> JvmTypes.jvmType(Type.RAW, null));
        assertEquals("no JVM carrier for Raw", raw.getMessage());
    }

    @Test
    void rawHasNoBoxedForm() {
        assertNull(JvmTypes.boxedPrim(Type.RAW));
    }
}
