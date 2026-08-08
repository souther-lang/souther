package souther.compiler;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Constructor;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The {@code "value"} envelope is what membership in a sum adds, not part of a newtype's own
 * representation (spec 10.3): a standalone newtype stays bare. So a declaration elsewhere that names
 * the type cannot change what the type writes, or reads, where it stands on its own.
 */
class AStandaloneNewtypeStaysBareWhenASumNamesItTest {

    private static final String ALONE = """
            module demo

            data Code = String
            """;

    private static final String NAMED_BY_A_SUM = """
            module demo

            data Code = String
            data Z = { z: Int }
            data S = Code | Z
            """;

    private BytesClassLoader compile(String module) {
        return new BytesClassLoader(Compiler.compile(module), getClass().getClassLoader());
    }

    /** A {@code Code} value, built through the class itself rather than through its decoder, so the
     *  encode direction is measured without the decode direction deciding what can be measured. */
    private static Object code(BytesClassLoader loader, String value) throws Exception {
        Constructor<?> ctor = loader.loadClass("demo.Code").getDeclaredConstructor(String.class);
        ctor.setAccessible(true);
        return ctor.newInstance(value);
    }

    @Test
    void aSumNamingTheNewtypeDoesNotChangeWhatItWrites() throws Exception {
        BytesClassLoader alone = compile(ALONE);
        BytesClassLoader named = compile(NAMED_BY_A_SUM);

        assertEquals("x", Codecs.encode(alone, "demo.Code", code(alone, "x")));
        assertEquals("x", Codecs.encode(named, "demo.Code", code(named, "x")),
                "a sum elsewhere names `Code`, which is nothing to do with what `Code` writes");
    }

    @Test
    void aSumNamingTheNewtypeDoesNotChangeWhatItReads() throws Exception {
        BytesClassLoader alone = compile(ALONE);
        BytesClassLoader named = compile(NAMED_BY_A_SUM);

        assertEquals("Ok", Codecs.decode(alone, "demo.Code", "x").getClass().getSimpleName());
        assertEquals("Ok", Codecs.decode(named, "demo.Code", "x").getClass().getSimpleName(),
                "a sum elsewhere names `Code`, which is nothing to do with what `Code` reads");
    }

    private static final String EVERY_SHAPE = """
            module demo

            data Rec = { x: Int }
            data Absent
            data Code = String
            data OverRec = Rec
            data S = Rec | Absent | Code | OverRec
            """;

    /** The four shapes a case can have, each read and written through its sum at the one form the
     *  rule gives it. {@code OverRec} is the row the shape of the derived encoder cannot answer: it
     *  writes an object and is wrapped all the same, because being wrapped is what being a newtype
     *  in a sum means and not what its representation came out as. */
    @Test
    void everyCaseShapeOfASumRoundTripsAtTheFormItsShapeGivesIt() throws Exception {
        BytesClassLoader loader = compile(EVERY_SHAPE);

        assertRoundTrips(loader, Map.of("x", 1L, "type", "Rec"));
        assertRoundTrips(loader, Map.of("type", "Absent"));
        assertRoundTrips(loader, Map.of("type", "Code", "value", "x"));
        assertRoundTrips(loader, Map.of("type", "OverRec", "value", Map.of("x", 1L)));
    }

    /** Each case still reads and writes its own form where it stands as itself, beside the sum. */
    @Test
    void everyCaseShapeStillReadsAndWritesItsOwnFormWhereItStandsAlone() throws Exception {
        BytesClassLoader loader = compile(EVERY_SHAPE);

        assertEquals(Map.of("x", 1L), encodedFrom(loader, "demo.Rec", Map.of("x", 1L)));
        assertEquals("x", encodedFrom(loader, "demo.Code", "x"));
        assertEquals(Map.of("x", 1L), encodedFrom(loader, "demo.OverRec", Map.of("x", 1L)));
    }

    private static void assertRoundTrips(BytesClassLoader loader, Map<String, Object> form)
            throws Exception {
        assertEquals(form, encodedFrom(loader, "demo.S", form),
                "what the sum wrote is what it reads back");
    }

    private static Object encodedFrom(BytesClassLoader loader, String type, Object form)
            throws Exception {
        return Codecs.encode(loader, type, Codecs.decoded(loader, type, form));
    }
}
