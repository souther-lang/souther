package souther.compiler;

import org.junit.jupiter.api.Test;

import java.time.LocalDate;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A date's parts, so a month boundary can be reached. {@code Date} offered only addDays / addMonths /
 * addYears / daysBetween, and the last day of a month needs the day-of-month of the date you start
 * from — so "end of next month", the ordinary Japanese payment term, could not be written at all
 * (issue #111). What could be written was a helper that looks right and returns the wrong date.
 *
 * <p>{@code year} and {@code day} are Ints in Elm ({@code Time.toYear} / {@code toDay}) and in .NET
 * ({@code DateTime.Year} / {@code Day}). {@code month} follows .NET rather than Elm's twelve-case
 * {@code Month}: {@code elm/time} has no month arithmetic, while {@code Date.addMonths} here counts
 * in months, so a named month would have to be converted back to add one.
 */
class CompileDatePartsTest {

    @Test
    void aDateAnswersItsYearMonthAndDay() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import Date ( year, month, day )

                data In = { on: Date }
                data Out = { y: Int, m: Int, d: Int }

                behavior parts : (i: In) -> Out constructs Out

                let parts (i) = Out { y = year(i.on), m = month(i.on), d = day(i.on) }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("on", LocalDate.parse("2026-07-26")));
        Object out = Codecs.apply(Emitted.behavior(loader, "demo", "parts").getConstructor().newInstance(), in);

        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(2026L, m.get("y"));
        assertEquals(7L, m.get("m"));
        assertEquals(26L, m.get("d"));
    }

    @Test
    void theMonthBoundaryIsReachableInTheLanguage() throws Exception {
        // what issue #111 could not write: the last day of the month after this one, whatever its
        // length — February and a 31-day month both come out right
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data In = { on: Date }
                data Out = { monthStart: Date, endOfThisMonth: Date, endOfNextMonth: Date }

                behavior bounds : (i: In) -> Out constructs Out

                let monthStart (d: Date): Date = Date.addDays(1 - Date.day(d), d)
                let endOfMonth (d: Date): Date =
                    Date.addDays(0 - 1, Date.addMonths(1, monthStart(d)))

                let bounds (i) = Out {
                    monthStart = monthStart(i.on),
                    endOfThisMonth = endOfMonth(i.on),
                    endOfNextMonth = endOfMonth(Date.addMonths(1, monthStart(i.on)))
                }
                """), getClass().getClassLoader());

        Object behavior = Emitted.behavior(loader, "demo", "bounds").getConstructor().newInstance();

        Map<?, ?> jan = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior,
                Codecs.decoded(loader, "demo.In", Map.of("on", LocalDate.parse("2026-01-15")))));
        assertEquals("2026-01-01", jan.get("monthStart"));
        assertEquals("2026-01-31", jan.get("endOfThisMonth"));
        assertEquals("2026-02-28", jan.get("endOfNextMonth"), "February, without counting its days");

        Map<?, ?> leap = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior,
                Codecs.decoded(loader, "demo.In", Map.of("on", LocalDate.parse("2024-01-31")))));
        assertEquals("2024-01-31", leap.get("endOfThisMonth"), "January ends on the 31st it started from");
        assertEquals("2024-02-29", leap.get("endOfNextMonth"), "a leap February, reached from the 31st");
    }

    @Test
    void aPartIsUsableInAnInvariant() throws Exception {
        // the parts are pure and non-recursive, so a data may state a rule over them
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data Quarter = { start: Date }
                    invariant Date.day(start) == 1

                data Out = { ok: Bool }

                behavior check : (q: Quarter) -> Out constructs Out
                let check (q) = Out { ok = true }
                """), getClass().getClassLoader());

        Object ok = Codecs.decode(loader, "demo.Quarter",
                Map.of("start", LocalDate.parse("2026-07-01")));
        Object bad = Codecs.decode(loader, "demo.Quarter",
                Map.of("start", LocalDate.parse("2026-07-02")));

        assertEquals("Ok", ok.getClass().getSimpleName());
        assertEquals("Err", bad.getClass().getSimpleName(), "the second of the month is not a start");
    }
}
