package souther.compiler;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import net.unit8.raoh.Err;
import net.unit8.raoh.Result;
import org.junit.jupiter.api.Test;

import tools.jackson.databind.json.JsonMapper;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a boundary is handed as a scalar is read as it is, and a value that could only be read by
 * changing it is refused at its path (spec §a-boundary-scalar-is-read-not-converted).
 *
 * <p>These are the readings a Raoh release decides and the language depends on, held here because
 * the release could change them without a line of this compiler changing. Before the release these
 * were pinned to, each answered a value: {@code 1.9} was the {@code Int} 1, {@code 2^70} was the
 * {@code Int} 0, a {@code java.sql.Date} was a day that depended on the JVM's default time zone, and a
 * {@code Map<String, Int>} took an {@code Integer} key. Each of those is a value nothing downstream
 * can tell from the value that was sent, which is what an {@code Int} that aborts on overflow
 * rather than wrapping exists to rule out. A Raoh that answers them again turns these red.
 */
class TheBoundaryRefusesWhatItCouldOnlyHaveReadWrongTest {

    private static final String MODEL = """
            module demo

            data In ={ n: Int, d: Decimal, at: Instant, day: Date, m: Map<String, Int> }
            data Out = { n: Int }

            behavior pass : (i: In) -> Out constructs Out
            let pass (i) = Out { n = i.n }
            """;

    private static final JsonMapper MAPPER = JsonMapper.builder().build();

    private static final BytesClassLoader LOADER = new BytesClassLoader(Compiler.compile(MODEL),
            TheBoundaryRefusesWhatItCouldOnlyHaveReadWrongTest.class.getClassLoader());

    private static Map<String, Object> with(String field, Object value) {
        Map<String, Object> raw = new HashMap<>();
        raw.put("n", 1L);
        raw.put("d", new BigDecimal("1.5"));
        raw.put("at", "2026-07-25T00:00:00Z");
        raw.put("day", "2026-07-25");
        raw.put("m", Map.of("k", 1L));
        raw.put(field, value);
        return raw;
    }

    private static Result<?> read(String field, Object value) throws Exception {
        return Codecs.decode(LOADER, "demo.In", with(field, value));
    }

    private static void assertRefusedAt(String pointer, Result<?> result, String what) {
        Err<?> err = assertInstanceOf(Err.class, result, what + " must be refused: " + result);
        assertEquals(pointer, err.issues().asList().get(0).path().toJsonPointer(), what);
    }

    /** An {@code Int} is read from a whole number a JDK integral type holds, and from nothing else. */
    @Test
    void anIntIsNotTruncatedNorWrappedNorTakenFromAFraction() throws Exception {
        assertRefusedAt("/n", read("n", 1.9), "1.9");
        assertRefusedAt("/n", read("n", 2.0), "2.0, which is a floating-point number");
        assertRefusedAt("/n", read("n", BigInteger.TWO.pow(70)), "2^70");
        assertRefusedAt("/n", read("n", new BigDecimal("5.5")), "5.5");
        assertRefusedAt("/n", read("n", new AtomicInteger(3)), "a number no JDK integral type is");
        assertRefusedAt("/n", read("n", "5"), "text");
        assertTrue(read("n", 5_000_000_000L).isOk());
        assertTrue(read("n", 5).isOk());
        assertTrue(read("n", new BigDecimal("5.00")).isOk(), "5.00 is the whole number 5");
    }

    /** The same at a JSON field, where a number is written with or without a point. */
    @Test
    void anIntAtAJsonFieldIsAnIntegerLiteralInRange() throws Exception {
        for (String refused : new String[] {
                "1.0", "1e2", "1.9", "9223372036854775808", "1180591620717411303424", "\"5\""}) {
            Result<?> r = Codecs.decode(LOADER, "demo.In", "jsonDecoder", MAPPER.readTree("""
                    {"n":%s,"d":1.5,"at":"2026-07-25T00:00:00Z","day":"2026-07-25","m":{"k":1}}
                    """.formatted(refused)));
            assertRefusedAt("/n", r, "the JSON number " + refused);
        }
        assertTrue(Codecs.decode(LOADER, "demo.In", "jsonDecoder", MAPPER.readTree("""
                {"n":9223372036854775807,"d":1.5,"at":"2026-07-25T00:00:00Z","day":"2026-07-25","m":{"k":1}}
                """)).isOk());
    }

    /** A {@code Decimal} that is no number is a failure at its path and not an exception out of the decoder. */
    @Test
    void aDecimalThatIsNoNumberIsAFailureAndNotAnException() throws Exception {
        assertRefusedAt("/d", read("d", Double.NaN), "NaN");
        assertRefusedAt("/d", read("d", Double.POSITIVE_INFINITY), "infinity");
        assertTrue(read("d", 1.5).isOk());
        assertTrue(read("d", 7L).isOk());
    }

    /** A temporal is a {@code java.time} value or its text; a {@code java.sql} one carries no zone. */
    @Test
    void aJavaSqlTemporalCarriesNoZoneAndIsRefused() throws Exception {
        assertRefusedAt("/day", read("day", new java.sql.Date(0L)), "a java.sql.Date");
        assertRefusedAt("/at", read("at", new java.sql.Timestamp(0L)), "a java.sql.Timestamp");
        assertTrue(read("day", java.time.LocalDate.of(2026, 7, 25)).isOk());
        assertTrue(read("at", java.time.Instant.EPOCH).isOk());
    }

    /** A boundary map has string keys, and one that has another is refused and not carried in. */
    @Test
    void aMapKeyedByStringTakesNoOtherKey() throws Exception {
        assertRefusedAt("/m", read("m", Map.of(1, 1L)), "an Integer key");
        assertTrue(read("m", Map.of("k", 1L)).isOk());
    }

    /**
     * A path is a JSON Pointer as RFC 6901 writes it: {@code /} and {@code ~} inside a key are
     * escaped, so the key {@code a/b} and the member {@code b} of {@code a} are two paths.
     */
    @Test
    void aPathEscapesTheCharactersAPointerWouldOtherwiseSplitOn() throws Exception {
        assertRefusedAt("/m/a~1b", read("m", Map.of("a/b", "x")), "a key holding a slash");
        assertRefusedAt("/m/a~0b", read("m", Map.of("a~b", "x")), "a key holding a tilde");
    }
}
