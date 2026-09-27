package souther.compiler;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import net.unit8.raoh.Err;
import net.unit8.raoh.Issue;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Result;
import org.jooq.Field;
import org.jooq.Record;
import org.jooq.SQLDialect;
import org.jooq.impl.DSL;
import org.junit.jupiter.api.Test;
import souther.compiler.generated.JsonBoundary;
import tools.jackson.databind.DeserializationFeature;
import tools.jackson.databind.node.ObjectNode;

import tools.jackson.databind.json.JsonMapper;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a boundary is handed is read as the value it determines, and a value the decoder would have
 * to make up is refused at its path (spec §a-boundary-scalar-is-read-not-converted,
 * §an-object-is-a-mapping, §decoder-error).
 *
 * <p>These are the readings a Raoh release decides and the language depends on, held here because
 * the release could change them without a line of this compiler changing. Before the release these
 * were pinned to, each answered a value: {@code 1.9} was the {@code Int} 1, {@code 2^70} was the
 * {@code Int} 0, a {@code java.sql.Date} was a day that depended on the JVM's default time zone, a
 * {@code Map<String, Int>} took an {@code Integer} key, and a {@code Decimal} read from a
 * {@code double} was the number that {@code double} prints and not the one that was written. Each of those is a value nothing downstream
 * can tell from the value that was sent, which is what an {@code Int} that aborts on overflow
 * rather than wrapping exists to rule out. A Raoh that answers them again turns these red. An
 * {@code Int} from {@code 5.00}, a {@code Decimal} from a {@code Double} and a {@code Decimal} from a
 * JSON node that holds a {@code double} are the readings the pinned Raoh takes and the language does
 * not: a decoder of this compiler asks first.
 */
class TheBoundaryRefusesWhatItCouldOnlyHaveReadWrongTest {

    private static final String MODEL = """
            module demo

            data In = { n: Int, d: Decimal, at: Instant, day: Date, m: Map<String, Int> }
            data Row = { n: Int, d: Decimal, at: Instant, day: Date }
            data Flag = { b: Bool }
            data Name = { s: String }
            data Out = { n: Int }

            behavior pass : (i: In) -> Out constructs Out
            let pass (i) = Out { n = i.n }

            behavior atAnInt : (n: Int) -> Out constructs Out
            let atAnInt (n) = Out { n = n }

            behavior atADecimal : (d: Decimal) -> Out constructs Out
            let atADecimal (d) = Out { n = 1 }
            """;

    /** A reader that keeps a fraction as the decimal it was written, and one that does not. */
    private static final JsonMapper EXACT = JsonMapper.builder()
            .enable(DeserializationFeature.USE_BIG_DECIMAL_FOR_FLOATS).build();
    private static final JsonMapper ROUNDING = JsonMapper.builder().build();

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

    /** Refused as a value of a kind the position does not read, which is Raoh's own code for it,
     *  whether Raoh or this compiler's decoder is the one that says it. */
    private static void assertMismatchAt(String pointer, Result<?> result, String what) {
        assertRefusedAt(pointer, result, what);
        Issue issue = ((Err<?>) result).issues().asList().get(0);
        assertEquals("type_mismatch", issue.code(), what + ": " + issue);
        assertTrue(issue.meta().containsKey("expected"),
                what + " carries what was expected, as Raoh's own does: " + issue.meta());
    }

    /**
     * An {@code Int} is read from an integer representation and from nothing else: not from a value
     * that is whole once a number that was written with a fraction is looked at, and not from one
     * that may have been rounded before it arrived. What a boundary is handed decides, and the
     * decoder does not infer afterwards what it meant.
     */
    @Test
    void anIntIsReadFromAnIntegerRepresentationAndNoOther() throws Exception {
        assertMismatchAt("/n", read("n", 1.9), "1.9");
        assertMismatchAt("/n", read("n", 5.0), "5.0, which may have been rounded before it arrived");
        assertMismatchAt("/n", read("n", BigInteger.TWO.pow(70)), "2^70");
        assertMismatchAt("/n", read("n", new BigDecimal("5.5")), "5.5");
        assertMismatchAt("/n", read("n", new BigDecimal("5.00")), "5.00, whose value is whole");
        assertMismatchAt("/n", read("n", new BigDecimal("5E+2")), "5E+2, whose value is whole");
        assertMismatchAt("/n", read("n", new AtomicInteger(3)), "a carrier that is no integer's");
        assertMismatchAt("/n", read("n", "5"), "text");
        assertTrue(read("n", 5_000_000_000L).isOk());
        assertTrue(read("n", 5).isOk());
        assertTrue(read("n", BigInteger.valueOf(5)).isOk());
        assertTrue(read("n", BigDecimal.valueOf(5)).isOk(), "a BigDecimal with no scale is an integer");
    }

    /** The same at a JSON field, where a number is written with or without a point. */
    @Test
    void anIntAtAJsonFieldIsAnIntegerLiteralInRange() throws Exception {
        for (String refused : new String[] {
                "1.0", "1e2", "1.9", "9223372036854775808", "1180591620717411303424", "\"5\""}) {
            Result<?> r = Codecs.decode(LOADER, "demo.In", "jsonDecoder", EXACT.readTree("""
                    {"n":%s,"d":1.5,"at":"2026-07-25T00:00:00Z","day":"2026-07-25","m":{"k":1}}
                    """.formatted(refused)));
            assertMismatchAt("/n", r, "the JSON number " + refused);
        }
        assertTrue(Codecs.decode(LOADER, "demo.In", "jsonDecoder", EXACT.readTree("""
                {"n":9223372036854775807,"d":1.5,"at":"2026-07-25T00:00:00Z","day":"2026-07-25","m":{"k":1}}
                """)).isOk());
    }

    /**
     * A {@code Decimal} is read from an exact number. A {@code Double} or a {@code Float} may have
     * been rounded before it arrived, and what it prints is the text of the binary value it was
     * rounded to; a number that is none is a failure at its path and not an exception out of the
     * decoder.
     */
    @Test
    void aDecimalIsReadFromAnExactNumberAndNoOther() throws Exception {
        assertMismatchAt("/d", read("d", 1.5), "1.5, a double that happens to be exact");
        assertMismatchAt("/d", read("d", 0.1f), "a float");
        assertMismatchAt("/d", read("d", Double.NaN), "NaN");
        assertMismatchAt("/d", read("d", Double.POSITIVE_INFINITY), "infinity");
        assertMismatchAt("/d", read("d", Float.NEGATIVE_INFINITY), "a float infinity");
        assertMismatchAt("/d", read("d", "1.5"), "text");
        // Said as what they are: no number at all, and not a number that was rounded.
        for (Object noNumber : new Object[] {Double.NaN, Double.POSITIVE_INFINITY}) {
            assertFalse(messageOf(read("d", noNumber)).contains("rounded"), String.valueOf(noNumber));
        }
        assertTrue(messageOf(read("d", 1.5)).contains("rounded"), "a finite double may have been");
        assertTrue(read("d", new BigDecimal("0.10000000000000001")).isOk());
        assertTrue(read("d", 7L).isOk());
        assertTrue(read("d", BigInteger.TEN).isOk());
    }

    /**
     * At a JSON field the reader decides how a fraction arrives. One that keeps it as a
     * {@code BigDecimal} hands the decoder the number that was written, whatever its digits; one that
     * parses it as a {@code double} has rounded {@code 0.10000000000000001} to {@code 0.1} before the
     * decoder sees it, and nothing can tell that from a literal that said {@code 0.1}, so it is
     * refused and not read as the number it is close to.
     */
    @Test
    void aDecimalAtAJsonFieldIsReadExactlyOrNotAtAll() throws Exception {
        String written = """
                {"n":1,"d":0.10000000000000001,"at":"2026-07-25T00:00:00Z","day":"2026-07-25","m":{"k":1}}
                """;
        Object exact = ((Ok<?>) Codecs.decode(LOADER, "demo.In", "jsonDecoder", EXACT.readTree(written)))
                .value();
        assertEquals(new BigDecimal("0.10000000000000001"), decimalOf(exact),
                "the number written, with every digit it was written with");
        assertMismatchAt("/d", Codecs.decode(LOADER, "demo.In", "jsonDecoder", ROUNDING.readTree(written)),
                "a fraction the reader parsed as a double");
        assertTrue(Codecs.decode(LOADER, "demo.In", "jsonDecoder", ROUNDING.readTree("""
                {"n":1,"d":15,"at":"2026-07-25T00:00:00Z","day":"2026-07-25","m":{"k":1}}
                """)).isOk(), "a whole number is an integer node, which is exact");
    }

    /**
     * A row of a relational source is read by the same rules: it reaches the same leaf decoders
     * through {@code recordDecoder()}, and a rule that held at a field and a key and not at a column
     * would be one more way in with a rule of its own.
     */
    @Test
    void aRowOfARelationalSourceIsReadByTheSameRules() throws Exception {
        assertTrue(readRow(5L, new BigDecimal("1.5"), "2026-07-25T00:00:00Z",
                java.time.LocalDate.of(2026, 7, 25)).isOk());
        assertMismatchAt("/n", readRow(new BigDecimal("5.00"), new BigDecimal("1.5"),
                "2026-07-25T00:00:00Z", "2026-07-25"), "5.00 in an integer column");
        assertMismatchAt("/d", readRow(5L, 1.5, "2026-07-25T00:00:00Z", "2026-07-25"),
                "a double in a decimal column");
        assertMismatchAt("/at", readRow(5L, new BigDecimal("1.5"), new java.sql.Timestamp(0L),
                "2026-07-25"), "a java.sql.Timestamp");
        assertMismatchAt("/day", readRow(5L, new BigDecimal("1.5"), "2026-07-25T00:00:00Z",
                new java.sql.Date(0L)), "a java.sql.Date");
        assertRefusedAt("/at", readRow(5L, new BigDecimal("1.5"), "2026-07-25t00:00:00z",
                "2026-07-25"), "text the language does not admit as an Instant");
    }

    private static Result<?> readRow(Object n, Object d, Object at, Object day) throws Exception {
        Field<Object> fn = DSL.field(DSL.name("n"), Object.class);
        Field<Object> fd = DSL.field(DSL.name("d"), Object.class);
        Field<Object> fat = DSL.field(DSL.name("at"), Object.class);
        Field<Object> fday = DSL.field(DSL.name("day"), Object.class);
        Record row = DSL.using(SQLDialect.DEFAULT).newRecord(fn, fd, fat, fday);
        row.set(fn, n);
        row.set(fd, d);
        row.set(fat, at);
        row.set(fday, day);
        return Codecs.decode(LOADER, "demo.Row", "recordDecoder", row);
    }

    /**
     * The runner reads a top-level argument through decoders of its own, and a reader that parsed a
     * fraction as a {@code double} hands one of them a node that is already rounded. It refuses it as
     * a generated {@code jsonDecoder()} does, and refuses {@code 5.0} for an {@code Int}.
     */
    @Test
    void aTopLevelArgumentTheRunnerReadsIsHeldToTheSameRules() throws Exception {
        assertInstanceOf(JsonBoundary.Read.Refused.class,
                Crossing.reading(MODEL, "demo", "atADecimal", "0.5"), "a fraction parsed as a double");
        assertInstanceOf(JsonBoundary.Read.Value.class,
                Crossing.reading(MODEL, "demo", "atADecimal", "5"), "a whole number is exact");
        assertInstanceOf(JsonBoundary.Read.Refused.class,
                Crossing.reading(MODEL, "demo", "atAnInt", "5.0"), "5.0 for an Int");
        assertInstanceOf(JsonBoundary.Read.Value.class,
                Crossing.reading(MODEL, "demo", "atAnInt", "5"));
    }

    /**
     * A {@code Bool} is read from a boolean and a {@code String} from text, and from nothing that
     * would have to be turned into one: a scalar of another kind is not made into the kind the
     * position asks for, whichever source hands it over. These two need no question of their own
     * because Raoh's decoders for them read one kind and no other; this is what holds them to that.
     */
    @Test
    void aBoolAndAStringAreReadFromTheirOwnKindAndNoOther() throws Exception {
        assertTrue(Codecs.decode(LOADER, "demo.Flag", Map.of("b", true)).isOk());
        assertMismatchAt("/b", Codecs.decode(LOADER, "demo.Flag", Map.of("b", "true")), "the text true");
        assertMismatchAt("/b", Codecs.decode(LOADER, "demo.Flag", Map.of("b", 1L)), "the number 1");
        assertTrue(Codecs.decode(LOADER, "demo.Flag", "jsonDecoder", EXACT.readTree("{\"b\":true}")).isOk());
        assertMismatchAt("/b", Codecs.decode(LOADER, "demo.Flag", "jsonDecoder",
                EXACT.readTree("{\"b\":\"true\"}")), "the JSON text true");
        assertMismatchAt("/b", Codecs.decode(LOADER, "demo.Flag", "jsonDecoder",
                EXACT.readTree("{\"b\":1}")), "the JSON number 1");

        assertTrue(Codecs.decode(LOADER, "demo.Name", Map.of("s", "x")).isOk());
        assertMismatchAt("/s", Codecs.decode(LOADER, "demo.Name", Map.of("s", 5L)), "the number 5");
        assertMismatchAt("/s", Codecs.decode(LOADER, "demo.Name", Map.of("s", true)), "the boolean true");
        assertMismatchAt("/s", Codecs.decode(LOADER, "demo.Name", "jsonDecoder",
                EXACT.readTree("{\"s\":5}")), "the JSON number 5");
        assertMismatchAt("/s", Codecs.decode(LOADER, "demo.Name", "jsonDecoder",
                EXACT.readTree("{\"s\":true}")), "the JSON boolean true");
    }

    /** A node that holds no number is refused as that too, and not as one that was rounded. */
    @Test
    void aJsonNodeThatIsNoNumberIsNotSaidToHaveBeenRounded() throws Exception {
        for (double noNumber : new double[] {Double.NaN, Double.NEGATIVE_INFINITY}) {
            ObjectNode node = (ObjectNode) EXACT.readTree("""
                    {"n":1,"at":"2026-07-25T00:00:00Z","day":"2026-07-25","m":{"k":1}}
                    """);
            node.put("d", noNumber);
            Result<?> r = Codecs.decode(LOADER, "demo.In", "jsonDecoder", node);
            assertMismatchAt("/d", r, "the JSON node " + noNumber);
            assertFalse(messageOf(r).contains("rounded"), messageOf(r));
        }
    }

    private static String messageOf(Result<?> result) {
        return ((Err<?>) result).issues().asList().get(0).message();
    }

    private static BigDecimal decimalOf(Object in) throws Exception {
        return (BigDecimal) in.getClass().getMethod("d").invoke(in);
    }

    /** A temporal is a {@code java.time} value or its text; a {@code java.sql} one carries no zone. */
    @Test
    void aJavaSqlTemporalCarriesNoZoneAndIsRefused() throws Exception {
        assertRefusedAt("/day", read("day", new java.sql.Date(0L)), "a java.sql.Date");
        assertRefusedAt("/at", read("at", new java.sql.Timestamp(0L)), "a java.sql.Timestamp");
        assertTrue(read("day", java.time.LocalDate.of(2026, 7, 25)).isOk());
        assertTrue(read("at", java.time.Instant.EPOCH).isOk());
    }

    /** A boundary map has string keys, and one that has another is refused and not carried in
     *  (spec §an-object-is-a-mapping). It is the object's rule and not a scalar's. */
    @Test
    void aMapKeyedByStringTakesNoOtherKey() throws Exception {
        assertRefusedAt("/m", read("m", Map.of(1, 1L)), "an Integer key");
        assertTrue(read("m", Map.of("k", 1L)).isOk());
    }

    /**
     * A path is a JSON Pointer as RFC 6901 writes it: {@code /} and {@code ~} inside a key are
     * escaped, so the key {@code a/b} and the member {@code b} of {@code a} are two paths
     * (spec §decoder-error). It is how an error is reported and not a scalar's rule.
     */
    @Test
    void aPathEscapesTheCharactersAPointerWouldOtherwiseSplitOn() throws Exception {
        assertRefusedAt("/m/a~1b", read("m", Map.of("a/b", "x")), "a key holding a slash");
        assertRefusedAt("/m/a~0b", read("m", Map.of("a~b", "x")), "a key holding a tilde");
    }
}
