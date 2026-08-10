package souther.compiler;

import souther.compiler.diag.msg.ExampleMessage;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;

/**
 * A fixture is read from what Souther writes, not from what a boundary carries. A date is written
 * {@code Date("2026-07-25")} and a date-time {@code DateTime("2026-07-25T09:00")}, and the compiler
 * parses the text where it stands — so by the time a fixture is a value, a temporal has been parsed.
 *
 * <p>The derived decoders also read ISO text, because that is how a temporal arrives over JSON and
 * out of a JDBC row. A fixture is built through those decoders and is not admitted by what they
 * additionally read: what a boundary carries a value as is not a second way to write a fixture.
 */
class ATemporalFixtureIsNotWrittenAsTextTest {

    private static final String DATETIME_IN = """
            module stamps exposing ( Stamp, stampAt )

            data Stamp = { at: DateTime }

            behavior stampAt : (d: DateTime) -> Stamp
                constructs Stamp
            let stampAt (d) = Stamp { at = d }
            """;

    private static final String DATE_IN = """
            module marks exposing ( Mark, markOn )

            data Mark = { on: Date }

            behavior markOn : (d: Date) -> Mark
                constructs Mark
            let markOn (d) = Mark { on = d }
            """;

    private static final String NEWTYPE_IN = """
            module moments exposing ( Moment, Held, hold )

            data Moment = DateTime
            data Held = { at: Moment }

            behavior hold : (m: Moment) -> Held
                constructs Held
            let hold (m) = Held { at = m }
            """;

    private static final String FIELD_IN = """
            module fields exposing ( Stamp, keep )

            data Stamp = { at: DateTime }

            behavior keep : (s: Stamp) -> Stamp
            let keep (s) = s
            """;

    private static final String HELPERS = """
            module helpers exposing ( Stamp, stampAt, keep )

            data Stamp = { at: DateTime }

            behavior stampAt : (d: DateTime) -> Stamp
                constructs Stamp
            let stampAt (d) = Stamp { at = d }

            behavior keep : (s: Stamp) -> Stamp
            let keep (s) = s

            let text (s: String) = s
            """;

    private static final String INJECTED = """
            module clock exposing ( Stamp, now, stampAt )

            data Stamp = { at: DateTime }

            behavior now : () -> DateTime

            behavior stampAt : () -> Stamp
                depends on now
                constructs Stamp
            let stampAt (now) = Stamp { at = now() }
            """;

    private static Diagnostic only(String model) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(model));
        assertEquals(1, e.diagnostics().size(), "one row, one diagnostic: " + e.getMessage());
        return e.diagnostics().get(0);
    }

    private static void refused(String model, String code, Class<? extends ExampleMessage> said) {
        Diagnostic d = only(model);
        assertEquals(code, d.code(), "a temporal written as text is a fixture that cannot be built: "
                + d.said());
        assertInstanceOf(said, d.said());
    }

    // --- every position a fixture writes a temporal at -------------------------------------------

    @Test
    void aStringDoesNotWriteADateTimeInput() {
        refused(DATETIME_IN + """

                example stampAt
                    | "text" : ("2026-07-20T09:00") -> Stamp
                """, "E1903", ExampleMessage.AnInputCouldNotBeBuilt.class);
    }

    @Test
    void aStringDoesNotWriteADateInput() {
        refused(DATE_IN + """

                example markOn
                    | "text" : ("2026-07-20") -> Mark
                """, "E1903", ExampleMessage.AnInputCouldNotBeBuilt.class);
    }

    @Test
    void aStringDoesNotWriteAPositionANewtypeMakesATemporal() {
        // The derived decoder for `Moment` reads text the same way its base does, so closing only the
        // primitive a position spells would leave every wrapper over one open.
        refused(NEWTYPE_IN + """

                example hold
                    | "text" : ("2026-07-20T09:00") -> Held
                """, "E1903", ExampleMessage.AnInputCouldNotBeBuilt.class);
    }

    @Test
    void aStringDoesNotWriteWhatATemporalNewtypeWraps() {
        // `Moment` wraps a `DateTime`, so it takes one. The reader used to parse this string itself,
        // which gave the same spelling one meaning inside a temporal newtype and another everywhere
        // else — a model body writing it is E1317 — and left the rule above with an exception.
        refused(NEWTYPE_IN + """

                example hold
                    | "text" : (Moment("2026-07-20T09:00")) -> Held
                """, "E1903", ExampleMessage.AnInputCouldNotBeBuilt.class);
    }

    @Test
    void aStringDoesNotWriteATemporalField() {
        refused(FIELD_IN + """

                example keep
                    | "text" : (Stamp { at = "2026-07-20T09:00" }) -> Stamp
                """, "E1903", ExampleMessage.AnInputCouldNotBeBuilt.class);
    }

    @Test
    void aStringDoesNotWriteAnExpectedTemporal() {
        refused("""
                module reads exposing ( Stamp, at )

                data Stamp = { at: DateTime }

                behavior at : (s: Stamp) -> DateTime
                let at (s) = s.at
                """ + """

                example at
                    | "text" : (Stamp { at = DateTime("2026-07-20T09:00") }) -> "2026-07-20T09:00"
                """, "E1903", ExampleMessage.TheExpectedValueCouldNotBeBuilt.class);
    }

    @Test
    void aStringDoesNotWriteAWithValueForATemporalDependency() {
        refused(INJECTED + """

                example stampAt
                    | "text" : () with now = "2026-07-20T09:00" -> Stamp
                """, "E1908", ExampleMessage.TheFakeValueCouldNotBeBuilt.class);
    }

    @Test
    void aStringDoesNotWriteAFakeOutputForATemporalDependency() {
        refused(INJECTED + """

                fake now
                    | () -> "2026-07-20T09:00"

                example stampAt
                    | "text" : () -> Stamp
                """, "E1908", ExampleMessage.TheFakeCouldNotBeBuilt.class);
    }

    @Test
    void aStringDoesNotWriteAnOptionalTemporalField() {
        // A `?` field holds the value itself, so what may stand there is what may stand at the type
        // it holds. Opening a newtype and stopping at an optional would leave the rule closed for one
        // way of writing a position and open for the other.
        refused("""
                module optional exposing ( Stamp, keep )

                data Stamp = { at: DateTime? }

                behavior keep : (s: Stamp) -> Stamp
                let keep (s) = s
                """ + """

                example keep
                    | "text" : (Stamp { at = "2026-07-20T09:00" })
                        -> Stamp { at = DateTime("2026-07-20T09:00") }
                """, "E1903", ExampleMessage.AnInputCouldNotBeBuilt.class);
    }

    @Test
    void aHelperAnsweringWithAStringDoesNotWriteATemporal() {
        // A row reaches the form a decoder reads two ways: from what the author wrote, and from a
        // value a helper returned. The rule is about the form, so it holds of both — a helper's
        // answer used to arrive as itself and be parsed by the decoder it was handed to.
        refused(HELPERS + """

                example stampAt
                    | "a helper's text" : (text("2026-07-20T09:00")) -> Stamp
                """, "E1903", ExampleMessage.AnInputCouldNotBeBuilt.class);
    }

    @Test
    void aHelperAnsweringWithAStringDoesNotWriteATemporalField() {
        // The same where the application stands inside a construction, so the rule is not one that
        // holds only of a whole fixture.
        refused(HELPERS + """

                example keep
                    | "a helper's text in a field" : (Stamp { at = text("2026-07-20T09:00") }) -> Stamp
                """, "E1903", ExampleMessage.AnInputCouldNotBeBuilt.class);
    }

    // --- what still writes one ------------------------------------------------------------------

    @Test
    void theWrittenTemporalFormsStillBuild() {
        assertDoesNotThrow(() -> Compiler.compile(DATETIME_IN + """

                example stampAt
                    | "a date-time" : (DateTime("2026-07-20T09:00")) -> Stamp
                """));
        assertDoesNotThrow(() -> Compiler.compile(DATE_IN + """

                example markOn
                    | "a date" : (Date("2026-07-20")) -> Mark
                """));
        assertDoesNotThrow(() -> Compiler.compile(NEWTYPE_IN + """

                example hold
                    | "a newtype over one" : (Moment(DateTime("2026-07-20T09:00"))) -> Held
                """));
        assertDoesNotThrow(() -> Compiler.compile(INJECTED + """

                example stampAt
                    | "a stand-in" : () with now = DateTime("2026-07-20T09:00") -> Stamp
                """));
    }

    @Test
    void anOptionalTemporalStillTakesOneAndStillTakesNone() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module optionalok exposing ( Stamp, keep )

                data Stamp = { at: DateTime? }

                behavior keep : (s: Stamp) -> Stamp
                let keep (s) = s

                example keep
                    | "a date-time" : (Stamp { at = DateTime("2026-07-20T09:00") })
                        -> Stamp { at = DateTime("2026-07-20T09:00") }
                    | "none" : (Stamp { at = None }) -> Stamp { at = None }
                """));
    }

    @Test
    void aHelperAnsweringWithATemporalStillWritesOne() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module helperok exposing ( Stamp, stampAt )

                data Stamp = { at: DateTime }

                behavior stampAt : (d: DateTime) -> Stamp
                    constructs Stamp
                let stampAt (d) = Stamp { at = d }

                let noon (d: DateTime) = d

                example stampAt
                    | "a helper's date-time" : (noon(DateTime("2026-07-20T09:00"))) -> Stamp
                """));
    }

    @Test
    void aStringStillWritesAString() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module names exposing ( Tag, label )

                data Tag = { text: String }

                behavior label : (t: String) -> Tag
                    constructs Tag
                let label (t) = Tag { text = t }

                example label
                    | "a string" : ("2026-07-20T09:00") -> Tag { text = "2026-07-20T09:00" }
                """));
    }
}
