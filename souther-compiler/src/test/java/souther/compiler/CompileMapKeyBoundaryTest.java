package souther.compiler;

import souther.compiler.diag.CompileException;
import net.unit8.raoh.Err;
import net.unit8.raoh.Result;
import org.junit.jupiter.api.Test;

import java.time.LocalDate;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code Map}'s key restriction is a boundary rule, not a rule about every map: a map is a JSON
 * object, whose keys are strings, so a key that crosses a decoder/encoder must render as and parse
 * from a bare string. Inside a behavior body nothing is rendered, so any key type is fine — which is
 * what {@code List.groupBy} was already producing while the compiler refused to let the same type be
 * written (issue #100). A temporal key crosses too: a {@code Date} field already travels as its ISO
 * form, so a {@code Date}-keyed map is a JSON object with ISO keys.
 */
class CompileMapKeyBoundaryTest {

    private static final String SALES = """
            module demo

            data Sale = { on: Date, amount: Int }
            data Bundle = { sales: List<Sale> }
            data Daily = { count: Int }

            behavior countOn : (b: Bundle, day: Date) -> Daily
                constructs Daily
            """;

    @Test
    void aMapKeyInsideABodyIsNotRestricted() {
        // `groupBy` builds this map either way; naming its type used to be the error
        Compiler.compile(SALES + """
                let countOn (b, day) = {
                    let g: Map<Date, List<Sale>> = List.groupBy((s) -> s.on, b.sales)
                    Daily { count = List.length(Map.get(day, g) |> Option.withDefault([])) }
                }
                """);
    }

    @Test
    void anIntBackedNewtypeKeyIsFineInsideABody() {
        Compiler.compile("""
                module demo

                data EmployeeNo = Int
                data Employee = { no: EmployeeNo, name: String }
                data Roster = { employees: List<Employee> }
                data Out = { count: Int }

                behavior countFor : (r: Roster, no: EmployeeNo) -> Out
                    constructs Out
                let countFor (r, no) = {
                    let byNo: Map<EmployeeNo, List<Employee>> =
                        List.groupBy((e) -> e.no, r.employees)
                    Out { count = List.length(Map.get(no, byNo) |> Option.withDefault([])) }
                }
                """);
    }

    @Test
    void aDateKeyedMapIsAFieldAndCrossesAsIsoKeys() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data Daily = { totals: Map<Date, Int> }
                data Out = { totals: Map<Date, Int> }

                behavior echo : (d: Daily) -> Out constructs Out

                let echo (d) = Out { totals = d.totals }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.Daily",
                Map.of("totals", Map.of("2026-01-01", 300L, "2026-01-02", 50L)));
        Object out = Codecs.apply(loader.loadClass("demo.Echo$Impl").getConstructor().newInstance(), in);

        assertEquals(Map.of("2026-01-01", 300L, "2026-01-02", 50L),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("totals"));
    }

    @Test
    void aDateKeyIsAValueOfThatTypeInsideTheBody() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( length )

                data Daily = { totals: Map<Date, Int> }
                data Out = { on: List<Date> }

                behavior days : (d: Daily) -> Out constructs Out

                let days (d) = Out { on = Map.keys(d.totals) }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.Daily", Map.of("totals", Map.of("2026-01-01", 300L)));
        Object out = Codecs.apply(loader.loadClass("demo.Days$Impl").getConstructor().newInstance(), in);

        assertEquals(List.of("2026-01-01"),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("on"));
    }

    @Test
    void aDateTimeKeyedMapCrossesToo() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data Readings = { at: Map<DateTime, Int> }
                data Out = { at: Map<DateTime, Int> }

                behavior echo : (r: Readings) -> Out constructs Out

                let echo (r) = Out { at = r.at }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.Readings",
                Map.of("at", Map.of("2026-01-01T09:00", 7L)));
        Object out = Codecs.apply(loader.loadClass("demo.Echo$Impl").getConstructor().newInstance(), in);

        assertEquals(Map.of("2026-01-01T09:00", 7L),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("at"));
    }

    @Test
    void aKeyThatIsNotADateFailsTheDecodeAtThatKey() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data Daily = { totals: Map<Date, Int> }
                """), getClass().getClassLoader());

        Result<?> r = Codecs.decode(loader, "demo.Daily", Map.of("totals", Map.of("nope", 1L)));

        assertTrue(r instanceof Err, "a key that is not an ISO date fails the decode");
        String at = ((Err<?>) r).issues().asList().get(0).path().toString();
        assertTrue(at.contains("totals") && at.contains("nope"), at);
    }

    @Test
    void aNestedDateKeyedMapCrossesTheSameWay() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data Book = { pages: List<Map<Date, Int>> }
                data Out = { pages: List<Map<Date, Int>> }

                behavior echo : (b: Book) -> Out constructs Out

                let echo (b) = Out { pages = b.pages }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.Book",
                Map.of("pages", List.of(Map.of("2026-01-01", 1L))));
        Object out = Codecs.apply(loader.loadClass("demo.Echo$Impl").getConstructor().newInstance(), in);

        assertEquals(List.of(Map.of("2026-01-01", 1L)),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("pages"));
    }

    @Test
    void anIntBackedNewtypeKeyCannotBeAField() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data EmployeeNo = Int
                data Roster = { byNo: Map<EmployeeNo, String> }
                """));

        assertTrue(e.getMessage().contains("EmployeeNo"), e.getMessage());
    }

    @Test
    void aProductDataKeyCannotBeAField() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Slot = { hour: Int, room: String }
                data Plan = { booked: Map<Slot, String> }
                """));

        assertTrue(e.getMessage().contains("Slot"), e.getMessage());
    }

    @Test
    void aNonBoundaryKeyNestedInAFieldIsCaughtToo() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data EmployeeNo = Int
                data Roster = { pages: List<Map<EmployeeNo, String>> }
                """));

        assertTrue(e.getMessage().contains("EmployeeNo"), e.getMessage());
    }

    @Test
    void aNonBoundaryKeyCannotBeABehaviorInput() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data EmployeeNo = Int
                data Out = { count: Int }

                behavior run : (byNo: Map<EmployeeNo, String>) -> Out constructs Out
                let run (byNo) = Out { count = 0 }
                """));

        assertTrue(e.getMessage().contains("EmployeeNo"), e.getMessage());
    }

    @Test
    void aNonBoundaryKeyCannotBeABehaviorOutput() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data EmployeeNo = Int
                data In = { n: Int }

                behavior run : (i: In) -> Map<EmployeeNo, String>
                let run (i) = Map.empty
                """));

        assertTrue(e.getMessage().contains("EmployeeNo"), e.getMessage());
    }

    @Test
    void aStringBackedNewtypeKeyStillCrosses() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data ProductId = String
                data Stock = { onHand: Map<ProductId, Int> }
                data Out = { onHand: Map<ProductId, Int> }

                behavior echo : (s: Stock) -> Out constructs Out

                let echo (s) = Out { onHand = s.onHand }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.Stock", Map.of("onHand", Map.of("P-01", 4L)));
        Object out = Codecs.apply(loader.loadClass("demo.Echo$Impl").getConstructor().newInstance(), in);

        assertEquals(Map.of("P-01", 4L),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("onHand"));
    }

    @Test
    void anExampleCanWriteADateKeyedFixture() {
        Compiler.compile("""
                module demo

                data Daily = { totals: Map<Date, Int> }
                data Out = { total: Int }

                behavior sum : (d: Daily) -> Out constructs Out

                let sum (d) = Out {
                    total = List.fold((acc, v) -> acc + v, 0, Map.values(d.totals))
                }

                example sum
                  | "adds the days up" :
                      (Daily { totals = [ (Date("2026-01-01"), 300), (Date("2026-01-02"), 50) ] })
                          -> Out { total = 350 }
                """);
    }

    /** A {@code LocalDate} reaching the neutral decoder as a key is the boundary's own form, so the
     *  in-language value is a {@code Date} and date arithmetic applies to it. */
    @Test
    void aDecodedDateKeyIsARealDate() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import Date ( addDays )
                import List ( map )

                data Daily = { totals: Map<Date, Int> }
                data Out = { next: List<Date> }

                behavior shift : (d: Daily) -> Out constructs Out

                let shift (d) = Out { next = map((k) -> addDays(1, k), Map.keys(d.totals)) }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.Daily", Map.of("totals", Map.of("2026-01-31", 1L)));
        Object out = Codecs.apply(loader.loadClass("demo.Shift$Impl").getConstructor().newInstance(), in);

        assertEquals(List.of(LocalDate.parse("2026-02-01").toString()),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("next"));
    }
}
