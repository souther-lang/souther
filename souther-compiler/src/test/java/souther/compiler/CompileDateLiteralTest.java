package souther.compiler;

import souther.compiler.diag.CompileException;
import org.junit.jupiter.api.Test;

import java.time.LocalDate;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A written date: {@code Date("2026-07-01")} / {@code DateTime("2026-07-01T09:00")}. The argument is
 * a string literal, parsed and checked when the module compiles, so a malformed date is a compile
 * error rather than a run-time one. It is the form an {@code example} fixture needs — without it a
 * behavior taking a date could not be examined at all.
 */
class CompileDateLiteralTest {

    @Test
    void aWrittenDateIsAValueAndFeedsDateArithmetic() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import Date ( addDays )

                data In = { n: Int }
                data Out = { start: Date, due: Date, at: DateTime }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    start = Date("2026-07-01"),
                    due = addDays(14, Date("2026-07-01")),
                    at = DateTime("2026-07-01T09:00:00")
                }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("n", 1L));
        Object out = Codecs.apply(
                loader.loadClass("demo.Run$Impl").getConstructor().newInstance(), in);

        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals("2026-07-01", m.get("start"));
        assertEquals("2026-07-15", m.get("due"));
        assertEquals("2026-07-01T09:00", m.get("at"));
    }

    @Test
    void aDateFixtureExaminesADateDrivenBehavior() throws Exception {
        // The payoff: the input and the expected output both carry dates, so the rule is fixed at
        // compile time by its examples like any other behavior.
        Compiler.compile("""
                module demo

                import Date ( daysBetween )

                data Due = { on: Date }
                data Overdue = { days: Int }
                data OnTime

                behavior check : (due: Due, today: Date) -> Overdue | OnTime
                    constructs Overdue, OnTime

                let check (due, today) = {
                    let late = daysBetween(due.on, today)
                    guard late > 0 else OnTime
                    Overdue { days = late }
                }

                example check
                    | "past the due date" :
                        (Due { on = Date("2026-07-01") }, Date("2026-07-25")) -> Overdue { days = 24 }
                    | "on the due date" :
                        (Due { on = Date("2026-07-25") }, Date("2026-07-25")) -> OnTime
                """);
    }

    @Test
    void aDateNewtypeTakesTheDateItWrapsInAFixture() throws Exception {
        // What it wraps, written as it is written anywhere: a newtype takes a value of its base, and
        // a `Date` is `Date("…")`. The reader used to take the base's written string here as well,
        // which no other position accepts and a model body is refused for (E1317).
        Compiler.compile("""
                module demo

                data 貸出日 = Date
                data Loan = { on: 貸出日 }
                data Echo = { on: 貸出日 }

                behavior repeatBack : (l: Loan) -> Echo constructs Echo

                let repeatBack (l) = Echo { on = l.on }

                example repeatBack
                    | "a written date survives the newtype" :
                        (Loan { on = 貸出日(Date("2026-07-01")) })
                            -> Echo { on = 貸出日(Date("2026-07-01")) }
                """);
    }

    @Test
    void aDateNewtypeDoesNotTakeTheBareStringItsBaseIsWrittenFrom() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data 貸出日 = Date
                data Loan = { on: 貸出日 }
                data Echo = { on: 貸出日 }

                behavior repeatBack : (l: Loan) -> Echo constructs Echo

                let repeatBack (l) = Echo { on = l.on }

                example repeatBack
                    | "a bare string" :
                        (Loan { on = 貸出日("2026-07-01") }) -> Echo { on = 貸出日(Date("2026-07-01")) }
                """));

        assertTrue(e.getMessage().contains("E1903"), e.getMessage());
    }

    @Test
    void aMalformedDateIsACompileError() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data In = { n: Int }
                data Out = { d: Date }
                behavior run : (i: In) -> Out constructs Out
                let run (i) = Out { d = Date("2026-13-45") }
                """));
        assertTrue(e.getMessage().contains("2026-13-45"), e.getMessage());
    }

    @Test
    void aDateMustBeWrittenNotComputed() {
        // Only a literal: the point of the form is that the compiler can check it.
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data In = { s: String }
                data Out = { d: Date }
                behavior run : (i: In) -> Out constructs Out
                let run (i) = Out { d = Date(i.s) }
                """));
        assertTrue(e.getMessage().contains("Date"), e.getMessage());
    }

    @Test
    void aWrittenDateWorksAtRunTimeThroughTheDecoder() throws Exception {
        // The value the backend emits is the same LocalDate the boundary decodes.
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import Date ( daysBetween )

                data In = { d: Date }
                data Out = { gap: Int }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { gap = daysBetween(Date("2026-07-01"), i.d) }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("d", LocalDate.parse("2026-07-11")));
        Object out = Codecs.apply(
                loader.loadClass("demo.Run$Impl").getConstructor().newInstance(), in);
        assertEquals(10L, ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("gap"));
    }
}
