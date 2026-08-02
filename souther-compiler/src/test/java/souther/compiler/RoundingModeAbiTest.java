package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.runtime.CEILING;
import souther.runtime.FLOOR;
import souther.runtime.HALF_UP;
import souther.runtime.RoundingMode;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.Comparator;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The handwritten {@code souther.runtime.RoundingMode} classes stand where generated ones would,
 * so their shape must match what the compiler emits for a unit-only sum — the static methods on
 * the sum, and the value contract on each case. Generated data is the reference: an enumeration is
 * compiled here and each observable is asserted pairwise against the handwritten type, so a change
 * to either side that the other does not follow fails this test rather than surfacing as a linkage
 * or behavior difference in a program.
 */
class RoundingModeAbiTest {

    private static final String MODULE = """
            module demo

            data Dir = NORTH | SOUTH | EAST | WEST
            """;

    private ClassLoader compiled() {
        return new BytesClassLoader(Compiler.compile(MODULE), getClass().getClassLoader());
    }

    /** The sum's static surface: {@code __tag}, {@code __order}, {@code __ordering}, with the
     * descriptors the emitter calls them by. */
    @Test
    void theSumCarriesTheSameStaticMethodsAsAGeneratedEnumeration() throws Exception {
        Class<?> generated = compiled().loadClass("demo.Dir");
        for (Class<?> sum : new Class<?>[] {generated, RoundingMode.class}) {
            Method tag = sum.getMethod("__tag", Object.class);
            assertEquals(String.class, tag.getReturnType(), sum.getName());
            assertTrue(Modifier.isStatic(tag.getModifiers()), sum.getName());
            Method order = sum.getMethod("__order", Object.class);
            assertEquals(int.class, order.getReturnType(), sum.getName());
            assertTrue(Modifier.isStatic(order.getModifiers()), sum.getName());
            Method ordering = sum.getMethod("__ordering");
            assertEquals(Comparator.class, ordering.getReturnType(), sum.getName());
            assertTrue(Modifier.isStatic(ordering.getModifiers()), sum.getName());
        }
    }

    /** {@code __tag} answers the case's name; {@code __order} its place in the declaration;
     * {@code __ordering} sorts by it. */
    @Test
    void tagAndOrderAnswerTheDeclarationTheSameWay() throws Exception {
        ClassLoader loader = compiled();
        Class<?> dir = loader.loadClass("demo.Dir");
        Object north = loader.loadClass("demo.NORTH").getField("INSTANCE").get(null);
        Object east = loader.loadClass("demo.EAST").getField("INSTANCE").get(null);

        assertEquals("NORTH", dir.getMethod("__tag", Object.class).invoke(null, north));
        assertEquals("HALF_UP", RoundingMode.__tag(HALF_UP.INSTANCE));

        assertEquals(0, dir.getMethod("__order", Object.class).invoke(null, north));
        assertEquals(2, dir.getMethod("__order", Object.class).invoke(null, east));
        assertEquals(0, RoundingMode.__order(HALF_UP.INSTANCE));
        assertEquals(5, RoundingMode.__order(CEILING.INSTANCE));

        @SuppressWarnings("unchecked")
        Comparator<Object> generated =
                (Comparator<Object>) dir.getMethod("__ordering").invoke(null);
        assertTrue(generated.compare(north, east) < 0);
        assertTrue(RoundingMode.__ordering().compare(HALF_UP.INSTANCE, FLOOR.INSTANCE) < 0);
    }

    /** The value contract of a unit case: a shared {@code INSTANCE} on a {@code Record} subclass,
     * equality by case, the stable hash, and the record-style text form. */
    @Test
    void aCaseCarriesTheSameValueContractAsAGeneratedUnit() throws Exception {
        ClassLoader loader = compiled();
        Class<?> north = loader.loadClass("demo.NORTH");
        Object generated = north.getField("INSTANCE").get(null);
        // the emitter reaches a unit only through INSTANCE, so constructor visibility is not part
        // of the shape; a second instance is made here only to observe the equality contract
        java.lang.reflect.Constructor<?> ctor = north.getDeclaredConstructor();
        ctor.setAccessible(true);
        Object another = ctor.newInstance();

        assertTrue(Record.class.isAssignableFrom(north));
        assertTrue(Record.class.isAssignableFrom(HALF_UP.class));

        assertEquals(generated, another);
        assertEquals(HALF_UP.INSTANCE, new HALF_UP());

        assertEquals(generated.hashCode(), HALF_UP.INSTANCE.hashCode());

        assertEquals("NORTH[]", generated.toString());
        assertEquals("HALF_UP[]", HALF_UP.INSTANCE.toString());
    }
}
