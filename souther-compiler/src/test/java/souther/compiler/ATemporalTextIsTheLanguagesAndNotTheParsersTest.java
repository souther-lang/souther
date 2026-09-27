package souther.compiler;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.msg.TypeMessage;
import souther.compiler.generated.JsonBoundary;
import souther.temporal.TemporalText;
import souther.temporal.TemporalText.Kind;
import souther.temporal.TemporalText.Refusal;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which text is a temporal is the language's (spec §temporal-text), and it is the same wherever the
 * text arrives.
 *
 * <p>Every row is put to a JSON field, a JSON map key, the runner's own decoders, and the bare-value
 * decoders a Java caller hands a {@code Map} to, and each answers what {@link TemporalText} answers.
 * A source literal is asked the same rows for the language it may write. What is being held is that no
 * path leaves the grammar to the parser behind it: {@code java.time} takes {@code t} and {@code z},
 * and a decimal point with no digits, and the Raoh a decoder is built against has taken them in one
 * release and refused them in the next.
 *
 * <p>No row is left out of any path. The bare-value decoders take a real temporal as itself and a
 * {@code String} as text, and Raoh parses that text inside itself, so a decoder stands in front of
 * it and asks {@link TemporalText} first (the decoder class's own {@code __date} and its siblings);
 * that is what lets a zero
 * fraction, which reads as a whole second once parsed, be refused there as it is everywhere else.
 * The same rows hold against a Raoh that takes more texts than the language does.
 */
class ATemporalTextIsTheLanguagesAndNotTheParsersTest {

    private static final JsonMapper MAPPER = JsonMapper.builder().build();

    /** What a temporal's text is at a boundary and in source. */
    private record Row(Kind kind, String text, Optional<Refusal> atBoundary, Optional<Refusal> inSource) {
        boolean readAtBoundary() {
            return atBoundary.isEmpty();
        }
    }

    private static Row row(Kind kind, String text, Refusal boundary, Refusal source) {
        return new Row(kind, text, Optional.ofNullable(boundary), Optional.ofNullable(source));
    }

    private static Row taken(Kind kind, String text) {
        return row(kind, text, null, null);
    }

    private static Row refused(Kind kind, String text, Refusal reason) {
        return row(kind, text, reason, reason);
    }

    private static final List<Row> ROWS = List.of(
            taken(Kind.DATE, "2026-07-25"),
            taken(Kind.DATE, "+12026-07-25"),
            taken(Kind.DATE, "-0001-01-01"),
            refused(Kind.DATE, "-0000-01-01", Refusal.MALFORMED),
            refused(Kind.DATE, "+2026-07-25", Refusal.MALFORMED),
            refused(Kind.DATE, "2026-7-25", Refusal.MALFORMED),
            refused(Kind.DATE, "2026-02-30", Refusal.MALFORMED),
            refused(Kind.DATE, "2026-07-25T00:00", Refusal.MALFORMED),

            taken(Kind.TIME, "09:30"),
            taken(Kind.TIME, "09:30:00"),
            refused(Kind.TIME, "09:30:00.", Refusal.MALFORMED),
            refused(Kind.TIME, "09:30:00.5", Refusal.SUB_SECOND),
            refused(Kind.TIME, "09:30:00.000", Refusal.SUB_SECOND),
            refused(Kind.TIME, "24:00", Refusal.MALFORMED),
            refused(Kind.TIME, "9:30", Refusal.MALFORMED),

            taken(Kind.DATETIME, "2026-07-25T09:30"),
            taken(Kind.DATETIME, "2026-07-25T09:30:00"),
            refused(Kind.DATETIME, "2026-07-25t09:30", Refusal.MALFORMED),
            refused(Kind.DATETIME, "2026-07-25 09:30", Refusal.MALFORMED),
            refused(Kind.DATETIME, "2026-07-25T09:30:00.000", Refusal.SUB_SECOND),
            refused(Kind.DATETIME, "2026-07-25T24:00", Refusal.MALFORMED),

            taken(Kind.INSTANT, "2026-07-25T00:00:00Z"),
            taken(Kind.INSTANT, "2026-07-25T00:00:00.123Z"),
            taken(Kind.INSTANT, "2026-07-25T24:00:00Z"),
            taken(Kind.INSTANT, "+12026-07-25T00:00:00Z"),
            row(Kind.INSTANT, "2026-07-25T09:00:00+09:00", null, Refusal.NOT_UTC),
            row(Kind.INSTANT, "2026-07-25T09:00:00+09:00:30", null, Refusal.NOT_UTC),
            refused(Kind.INSTANT, "2026-07-25T24:00:00.5Z", Refusal.MALFORMED),
            refused(Kind.INSTANT, "2026-07-25T00:00:00z", Refusal.MALFORMED),
            refused(Kind.INSTANT, "2026-07-25T00:00:00.Z", Refusal.MALFORMED),
            refused(Kind.INSTANT, "2026-07-25T00:00Z", Refusal.MALFORMED),
            refused(Kind.INSTANT, "2026-07-25T00:00:00", Refusal.MALFORMED),
            refused(Kind.INSTANT, "2026-07-25T00:00:00+9:00", Refusal.MALFORMED),
            refused(Kind.INSTANT, "2026-07-25T00:00:00+19:00", Refusal.MALFORMED),
            refused(Kind.INSTANT, "2026-06-30T23:59:60Z", Refusal.LEAP_SECOND),

            // The ends of each domain, each in its own: an Instant reaches a year past a Date on
            // either side, and a carry from an hour 24 or an offset is asked of the moment it names.
            taken(Kind.DATE, "+999999999-12-31"),
            taken(Kind.DATE, "-999999999-01-01"),
            taken(Kind.DATE, "2000-02-29"),
            refused(Kind.DATE, "+1000000000-01-01", Refusal.MALFORMED),
            refused(Kind.DATE, "1900-02-29", Refusal.MALFORMED),
            taken(Kind.DATETIME, "+999999999-12-31T23:59:59"),
            refused(Kind.DATETIME, "-1000000000-01-01T00:00", Refusal.MALFORMED),
            taken(Kind.INSTANT, "-1000000000-01-01T00:00:00Z"),
            taken(Kind.INSTANT, "+1000000000-12-31T23:59:59.999999999Z"),
            taken(Kind.INSTANT, "+999999999-12-31T24:00:00Z"),
            row(Kind.INSTANT, "-999999999-01-01T00:00:00+18:00", null, Refusal.NOT_UTC),
            row(Kind.INSTANT, "2026-07-25T24:00:00+09:00", null, Refusal.NOT_UTC),
            refused(Kind.INSTANT, "-1000000001-12-31T23:59:59Z", Refusal.MALFORMED),
            refused(Kind.INSTANT, "+1000000001-01-01T00:00:00Z", Refusal.MALFORMED),
            refused(Kind.INSTANT, "+1000000000-12-31T24:00:00Z", Refusal.MALFORMED),
            refused(Kind.INSTANT, "-1000000000-01-01T00:00:00+01:00", Refusal.MALFORMED),
            refused(Kind.INSTANT, "2026-02-30T00:00:00Z", Refusal.MALFORMED));

    /** The table is what the language says, before any path is asked. */
    @Test
    void theLanguageAnswersEveryRow() {
        for (Row r : ROWS) {
            assertEquals(r.atBoundary(), TemporalText.atBoundary(r.kind(), r.text()),
                    r.kind() + " " + r.text() + " at a boundary");
            assertEquals(r.inSource(), TemporalText.inSource(r.kind(), r.text()),
                    r.kind() + " " + r.text() + " in source");
        }
    }

    /** What source may write is inside what a boundary reads. */
    @Test
    void whatSourceWritesIsInsideWhatABoundaryReads() {
        for (Row r : ROWS) {
            if (r.inSource().isEmpty()) {
                assertTrue(r.atBoundary().isEmpty(), r.kind() + " " + r.text());
            }
        }
    }

    private static final String MODEL = """
            module demo

            data In = { d: Date, t: Time, dt: DateTime, at: Instant }
            data Keyed = { d: Map<Date, Int>, t: Map<Time, Int>, dt: Map<DateTime, Int>,
                           at: Map<Instant, Int> }
            data Out = { n: Int }

            behavior atADate : (v: Date) -> Out constructs Out
            let atADate (v) = Out { n = 1 }

            behavior atATime : (v: Time) -> Out constructs Out
            let atATime (v) = Out { n = 1 }

            behavior atADateTime : (v: DateTime) -> Out constructs Out
            let atADateTime (v) = Out { n = 1 }

            behavior atAnInstant : (v: Instant) -> Out constructs Out
            let atAnInstant (v) = Out { n = 1 }
            """;

    private static final Map<Kind, String> FIELD = Map.of(
            Kind.DATE, "d", Kind.TIME, "t", Kind.DATETIME, "dt", Kind.INSTANT, "at");

    private static final Map<Kind, String> BEHAVIOR = Map.of(
            Kind.DATE, "atADate", Kind.TIME, "atATime", Kind.DATETIME, "atADateTime",
            Kind.INSTANT, "atAnInstant");

    private static final Map<String, String> USUAL = Map.of(
            "d", "2026-07-25", "t", "09:30:00", "dt", "2026-07-25T09:30:00",
            "at", "2026-07-25T00:00:00Z");

    /** A boundary reads what the language reads, at a field and under a key, whatever the path. */
    @Test
    void everyPathAtABoundaryReadsWhatTheLanguageReads() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(MODEL),
                ATemporalTextIsTheLanguagesAndNotTheParsersTest.class.getClassLoader());
        for (Row r : ROWS) {
            String field = FIELD.get(r.kind());
            Map<String, Object> fields = new HashMap<>(USUAL);
            fields.put(field, r.text());
            Map<String, Object> keys = new HashMap<>();
            USUAL.forEach((k, v) -> keys.put(k, Map.of(k.equals(field) ? r.text() : v, 1L)));
            String where = r.kind() + " " + r.text();

            JsonNode fieldsJson = MAPPER.valueToTree(fields);
            JsonNode keysJson = MAPPER.valueToTree(keys);
            assertEquals(r.readAtBoundary(),
                    Codecs.decode(loader, "demo.In", "jsonDecoder", fieldsJson).isOk(),
                    where + " at a JSON field");
            assertEquals(r.readAtBoundary(),
                    Codecs.decode(loader, "demo.Keyed", "jsonDecoder", keysJson).isOk(),
                    where + " under a JSON key");

            assertEquals(r.readAtBoundary(), Codecs.decode(loader, "demo.In", fields).isOk(),
                    where + " at a bare-value field");
            assertEquals(r.readAtBoundary(), Codecs.decode(loader, "demo.Keyed", keys).isOk(),
                    where + " under a bare-value key");
        }
    }

    /**
     * What a boundary reads is written back as text source may write, and read again as the same
     * value: {@code C ⊆ S ⊆ B}, asked of the encoder this compiler derives and not of
     * {@code toString}. A text that names a moment another way (an offset, an hour 24) comes back in
     * the one form, and the text that comes back is the one the value is written as.
     */
    @Test
    void whatTheEncoderWritesForAValueABoundaryReadIsReadBackAndWrittenInSource() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(MODEL),
                ATemporalTextIsTheLanguagesAndNotTheParsersTest.class.getClassLoader());
        for (Row r : ROWS) {
            if (!r.readAtBoundary()) {
                continue;
            }
            String field = FIELD.get(r.kind());
            Map<String, Object> raw = new HashMap<>(USUAL);
            raw.put(field, r.text());
            String where = r.kind() + " " + r.text();

            Object value = Codecs.decoded(loader, "demo.In", raw);
            Map<?, ?> written = (Map<?, ?>) Codecs.encode(loader, "demo.In", value);
            String text = String.valueOf(written.get(field));
            assertEquals(Optional.empty(), TemporalText.inSource(r.kind(), text),
                    where + " is written back as " + text + ", which source may not write");
            assertEquals(value, Codecs.decoded(loader, "demo.In", MAPPER.convertValue(written, Map.class)),
                    where + " does not read back as the value it was written from");
        }
    }

    /** The one worked example the specification gives: an offset names a moment, written in UTC. */
    @Test
    void anOffsetIsWrittenBackAsTheSameMomentInUtc() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(MODEL),
                ATemporalTextIsTheLanguagesAndNotTheParsersTest.class.getClassLoader());
        Map<String, Object> raw = new HashMap<>(USUAL);
        raw.put("at", "2026-07-25T09:00:00+09:00");
        Map<?, ?> written = (Map<?, ?>) Codecs.encode(loader, "demo.In",
                Codecs.decoded(loader, "demo.In", raw));
        assertEquals("2026-07-25T00:00:00Z", String.valueOf(written.get("at")));
    }

    /** The runner reads a top-level argument by the same language. */
    @Test
    void theRunnerReadsWhatTheLanguageReads() throws Exception {
        for (Row r : ROWS) {
            JsonBoundary.Read read = Crossing.reading(MODEL, "demo", BEHAVIOR.get(r.kind()),
                    MAPPER.writeValueAsString(r.text()));
            assertEquals(r.readAtBoundary(), read instanceof JsonBoundary.Read.Value,
                    r.kind() + " " + r.text() + " as an argument");
        }
    }

    /** Source writes what the language writes, and says why where it does not. */
    @Test
    void sourceWritesWhatTheLanguageWrites() {
        for (Row r : ROWS) {
            String where = r.kind() + " " + r.text() + " in source";
            String type = switch (r.kind()) {
                case DATE -> "Date";
                case TIME -> "Time";
                case DATETIME -> "DateTime";
                case INSTANT -> "Instant";
            };
            String source = """
                    module demo

                    data In = { n: Int }
                    data Out = { v: %s }

                    behavior go : (i: In) -> Out constructs Out
                    let go (i) = Out { v = %s("%s") }
                    """.formatted(type, type, r.text());
            if (r.inSource().isEmpty()) {
                Compiler.compile(source);
                continue;
            }
            CompileException e = assertThrows(CompileException.class,
                    () -> Compiler.compile(source), where);
            Class<?> said = switch (r.inSource().get()) {
                case MALFORMED -> TypeMessage.ThatIsNotATemporalOfThatKind.class;
                case SUB_SECOND -> TypeMessage.ATimeOfDayIsWrittenToTheSecond.class;
                case LEAP_SECOND -> TypeMessage.ALeapSecondIsNotAMoment.class;
                case NOT_UTC -> TypeMessage.AnInstantIsWrittenInUtc.class;
            };
            assertInstanceOf(said, e.diagnostic().said(), where + ": " + e.getMessage());
        }
    }
}
