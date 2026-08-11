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

    // --- a newtype is a key exactly when what it wraps is one (issue #636) ---------------------

    /** Compiles {@code body} onto the demo module and echoes {@code in} through {@code echo}, which
     *  is the round trip: the field's keys are decoded into the key type and written back out. */
    private Object echoed(String body, Object in) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(
                Compiler.compile("module demo\n\n" + body), getClass().getClassLoader());
        Object decoded = Codecs.decoded(loader, "demo.In", Map.of("m", in));
        Object out = Codecs.apply(
                loader.loadClass("demo.Echo$Impl").getConstructor().newInstance(), decoded);
        return ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("m");
    }

    private static String echoing(String key, String declarations) {
        return declarations + """

                data In = { m: Map<%s, Int> }
                data Out = { m: Map<%s, Int> }

                behavior echo : (i: In) -> Out constructs Out

                let echo (i) = Out { m = i.m }
                """.formatted(key, key);
    }

    @Test
    void aNewtypeOverADateKeysAMapAtTheBoundary() throws Exception {
        assertEquals(Map.of("2026-01-01", 3L),
                echoed(echoing("LoanDate", "data LoanDate = Date"), Map.of("2026-01-01", 3L)));
    }

    @Test
    void aNewtypeOverADateTimeKeysAMapAtTheBoundary() throws Exception {
        assertEquals(Map.of("2026-01-01T09:00", 7L),
                echoed(echoing("StampedAt", "data StampedAt = DateTime"),
                        Map.of("2026-01-01T09:00", 7L)));
    }

    @Test
    void aNewtypeOverAnEnumerationKeysAMapAtTheBoundary() throws Exception {
        assertEquals(Map.of("Won", 2L),
                echoed(echoing("Bracket", """
                        data Won
                        data Lost
                        data Outcome = Won | Lost
                        data Bracket = Outcome"""), Map.of("Won", 2L)));
    }

    @Test
    void aNewtypeOverAStringBackedNewtypeKeysAMapAtTheBoundary() throws Exception {
        assertEquals(Map.of("P-01", 4L),
                echoed(echoing("Legacy", """
                        data ProductId = String
                        data Legacy = ProductId"""), Map.of("P-01", 4L)));
    }

    /** Three wrappers deep, so what is held is that the rule recurses rather than that it unwraps
     *  one level more than it used to. */
    @Test
    void theRuleHoldsThreeWrappersDeep() throws Exception {
        assertEquals(Map.of("2026-01-01", 1L),
                echoed(echoing("C", """
                        data A = Date
                        data B = A
                        data C = B"""), Map.of("2026-01-01", 1L)));
    }

    /** A wrapped key is decoded by the outermost type's own decoder, which delegates inward — so an
     *  invariant declared on the base still runs on the key, and fails at that key's path. */
    @Test
    void aWrappedKeyRunsTheInvariantOfWhatItWraps() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data Code = String
                invariant String.length(value) == 4

                data Legacy = Code
                data In = { m: Map<Legacy, Int> }
                """), getClass().getClassLoader());

        Result<?> r = Codecs.decode(loader, "demo.In", Map.of("m", Map.of("AB", 1L)));

        assertTrue(r instanceof Err, "the key \"AB\" is not length 4, so the decode fails");
        String at = ((Err<?>) r).issues().asList().get(0).path().toString();
        assertTrue(at.contains("m") && at.contains("AB"), at);
    }

    /** A map inside a collection is emitted down the element-encoder path rather than the field one,
     *  so a wrapped key has to be rendered there too. */
    @Test
    void aWrappedKeyRendersInANestedMapToo() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data LoanDate = Date
                data Book = { pages: List<Map<LoanDate, Int>> }
                data Out = { pages: List<Map<LoanDate, Int>> }

                behavior echo : (b: Book) -> Out constructs Out

                let echo (b) = Out { pages = b.pages }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.Book",
                Map.of("pages", List.of(Map.of("2026-01-01", 1L))));
        Object out = Codecs.apply(loader.loadClass("demo.Echo$Impl").getConstructor().newInstance(), in);

        assertEquals(List.of(Map.of("2026-01-01", 1L)),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("pages"));
    }

    /** The refusal is the base's, and wrapping does not launder it: an {@code Int} is a JSON number
     *  in a field, so it is not a key, and neither is anything written round it. */
    @Test
    void aNewtypeOverAnIntBackedNewtypeStillCannotBeAField() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data EmployeeNo = Int
                data Legacy = EmployeeNo
                data Roster = { byNo: Map<Legacy, String> }
                """));

        assertTrue(e.getMessage().contains("Legacy"), e.getMessage());
    }

    @Test
    void anExampleCanWriteAWrappedDateKeyedFixture() {
        Compiler.compile("""
                module demo

                data LoanDate = Date
                data Loans = { totals: Map<LoanDate, Int> }
                data Out = { total: Int }

                behavior sum : (l: Loans) -> Out constructs Out

                let sum (l) = Out {
                    total = List.fold((acc, v) -> acc + v, 0, Map.values(l.totals))
                }

                example sum
                  | "adds the days up" :
                      (Loans { totals = [ (LoanDate(Date("2026-01-01")), 300)
                                        , (LoanDate(Date("2026-01-02")), 50) ] })
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
