package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.msg.TypeMessage;

import java.time.Instant;
import java.time.LocalDateTime;
import java.time.LocalTime;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a written temporal may say, and what a boundary will take (issue #623).
 *
 * <p>{@code Time} and {@code DateTime} are held to the second, and {@code Instant} to UTC. Both
 * refusals are about the same thing: text that says more than the type holds. Dropping the excess
 * instead would be worse than refusing it, because a value quietly rounded reads downstream as the
 * value that was sent and nothing later can tell the two apart — which is the defect this whole
 * issue turned out to be about, in its other half.
 */
class AWrittenTemporalSaysNoMoreThanItsTypeHoldsTest {

    @Test
    void aWrittenTimeOfDayCarriesNoFractionOfASecond() {
        for (String written : List.of(
                "DateTime(\"2026-07-01T09:30:45.123\")",
                "DateTime(\"2026-07-01T09:30:45.000000001\")",
                "Time(\"09:30:45.5\")")) {
            CompileException e = refuses(written);
            assertInstanceOf(TypeMessage.ATimeOfDayIsWrittenToTheSecond.class, e.diagnostic().said(),
                    written + " — " + e.getMessage());
        }
    }

    @Test
    void aWrittenTimeOfDayToTheSecondIsAccepted() {
        for (String written : List.of(
                "DateTime(\"2026-07-01T09:30\")", "DateTime(\"2026-07-01T09:30:45\")",
                "Time(\"09:30\")", "Time(\"09:30:45\")", "Date(\"2026-07-01\")")) {
            accepts(written);
        }
    }

    @Test
    void aWrittenInstantIsInUtc() {
        for (String written : List.of(
                "Instant(\"2026-07-01T09:30:45+09:00\")",
                "Instant(\"2026-07-01T09:30:45-05:00\")")) {
            CompileException e = refuses(written);
            assertInstanceOf(TypeMessage.AnInstantIsWrittenInUtc.class, e.diagnostic().said(),
                    written + " — " + e.getMessage());
        }
    }

    /** An {@code Instant} keeps a sub-second reading — that is what it is for — and text that is no
     *  instant at all is still reported as that rather than as a zone it does not carry. */
    @Test
    void aWrittenInstantKeepsItsFractionAndIsStillReadAsAnInstant() {
        accepts("Instant(\"2026-07-01T09:30:45.123456789Z\")");
        accepts("Instant(\"2026-07-01T09:30:45Z\")");
        CompileException e = refuses("Instant(\"not a moment\")");
        assertInstanceOf(TypeMessage.ThatIsNotATemporalOfThatKind.class, e.diagnostic().said(),
                e.getMessage());
    }

    /** The boundary makes the same refusal, as a decode failure at the field's path rather than as a
     *  value rounded on the way in. */
    @Test
    void aBoundaryRefusesASubSecondReadingRatherThanDroppingIt() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data In = { at: DateTime, of: Time }
                data Out = { at: DateTime, of: Time }

                behavior pass : (i: In) -> Out constructs Out

                let pass (i) = Out { at = i.at, of = i.of }
                """), getClass().getClassLoader());

        // to the second: through, unchanged
        Object in = Codecs.decoded(loader, "demo.In",
                Map.of("at", LocalDateTime.parse("2026-07-01T09:30:45"),
                        "of", LocalTime.parse("09:30:45")));
        Map<?, ?> out = assertInstanceOf(Map.class, Codecs.encode(loader, "demo.Out",
                Codecs.apply(loader.loadClass("demo.Pass$Impl").getConstructor().newInstance(), in)));
        assertEquals("2026-07-01T09:30:45", String.valueOf(out.get("at")));

        // finer than a second: refused, at the field that carried it
        net.unit8.raoh.Result<?> refused = Codecs.decode(loader, "demo.In",
                Map.of("at", LocalDateTime.parse("2026-07-01T09:30:45.123"),
                        "of", LocalTime.parse("09:30:45")));
        assertTrue(!refused.isOk(),
                "a DateTime carrying a fraction of a second must not be admitted");
        assertTrue(String.valueOf(refused).contains("at"),
                "the refusal names the field it came in at: " + refused);

        net.unit8.raoh.Result<?> refusedTime = Codecs.decode(loader, "demo.In",
                Map.of("at", LocalDateTime.parse("2026-07-01T09:30:45"),
                        "of", LocalTime.parse("09:30:45.5")));
        assertTrue(!refusedTime.isOk(),
                "a Time carrying a fraction of a second must not be admitted either");
    }

    /** An {@code Instant} crosses with its fraction intact, which is the difference that earns it. */
    @Test
    void aBoundaryTakesAnInstantsFraction() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data In = { at: Instant }
                data Out = { at: Instant }

                behavior pass : (i: In) -> Out constructs Out

                let pass (i) = Out { at = i.at }
                """), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In",
                Map.of("at", Instant.parse("2026-07-01T09:30:45.123456789Z")));
        Map<?, ?> out = assertInstanceOf(Map.class, Codecs.encode(loader, "demo.Out",
                Codecs.apply(loader.loadClass("demo.Pass$Impl").getConstructor().newInstance(), in)));
        assertEquals("2026-07-01T09:30:45.123456789Z", String.valueOf(out.get("at")));
    }

    private static CompileException refuses(String written) {
        return assertThrows(CompileException.class, () -> Compiler.compile(model(written)),
                written + " must be refused");
    }

    private static void accepts(String written) {
        Compiler.compile(model(written));
    }

    private static String model(String written) {
        return """
                module demo

                data In = { n: Int }
                data Out = { n: Int }

                behavior use : (i: In) -> Out constructs Out

                let use (i) = {
                    let written = %s
                    Out { n = i.n }
                }
                """.formatted(written);
    }
}
