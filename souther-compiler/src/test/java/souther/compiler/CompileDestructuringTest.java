package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An irrefutable pattern — a tuple, a newtype constructor, a record's fields — may be written
 * wherever a name is bound, not only in a {@code match} arm: a {@code let} statement, a helper's
 * parameter, a lambda's parameter. A refutable one (a sum's case, {@code Some x}) stays in
 * {@code match}, which is where a value can fail to have the shape.
 */
class CompileDestructuringTest {

    private BytesClassLoader load(String src) {
        return new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
    }

    private Object apply(BytesClassLoader loader, String cls, Object in) throws Exception {
        Object b = loader.loadClass("demo." + cls + "$Impl").getConstructor().newInstance();
        return Codecs.apply(b, in);
    }

    @Test
    void aLetOpensANewtype() throws Exception {
        BytesClassLoader loader = load("""
                module demo
                import List ( length )
                data Tags = List<String>

                behavior countTags : (t: Tags) -> Int
                let countTags (t) = {
                    let Tags(xs) = t
                    length(xs)
                }
                """);

        assertEquals(2L, apply(loader, "CountTags",
                Codecs.decoded(loader, "demo.Tags", List.of("a", "b"))));
    }

    @Test
    void aLetOpensNestedNewtypes() throws Exception {
        BytesClassLoader loader = load("""
                module demo
                data Email = String
                data Activated = Email
                data Out = { v: String }

                behavior addr : (a: Activated) -> Out constructs Out
                let addr (a) = {
                    let Activated(Email(s)) = a
                    Out { v = s }
                }
                """);

        assertEquals(java.util.Map.of("v", "a@example.com"), Codecs.encode(loader, "demo.Out",
                apply(loader, "Addr", Codecs.decoded(loader, "demo.Activated", "a@example.com"))));
    }

    @Test
    void aLetOpensARecordsFields() throws Exception {
        BytesClassLoader loader = load("""
                module demo
                data Line = { sku: String, qty: Int }
                data Out = { v: Int }

                behavior twice : (l: Line) -> Out constructs Out
                let twice (l) = {
                    let { qty } = l
                    Out { v = qty * 2 }
                }
                """);

        assertEquals(java.util.Map.of("v", 6L), Codecs.encode(loader, "demo.Out",
                apply(loader, "Twice", Codecs.decoded(loader, "demo.Line",
                        java.util.Map.of("sku", "s-1", "qty", 3L)))));
    }

    @Test
    void aLetRenamesADestructuredField() throws Exception {
        BytesClassLoader loader = load("""
                module demo
                data Line = { sku: String, qty: Int }
                data Out = { v: Int }

                behavior twice : (l: Line) -> Out constructs Out
                let twice (l) = {
                    let { qty = n } = l
                    Out { v = n * 2 }
                }
                """);

        assertEquals(java.util.Map.of("v", 6L), Codecs.encode(loader, "demo.Out",
                apply(loader, "Twice", Codecs.decoded(loader, "demo.Line",
                        java.util.Map.of("sku", "s-1", "qty", 3L)))));
    }

    @Test
    void aLambdaParameterOpensANewtype() throws Exception {
        BytesClassLoader loader = load("""
                module demo
                import List ( length, map )
                data Tags = List<String>
                data In = { groups: List<Tags> }
                data Out = { counts: List<Int> }

                behavior countAll : (i: In) -> Out constructs Out
                let countAll (i) = Out { counts = map((Tags(xs)) -> length(xs), i.groups) }
                """);

        Object in = Codecs.decoded(loader, "demo.In",
                java.util.Map.of("groups", List.of(List.of("a", "b"), List.of("c"))));
        assertEquals(java.util.Map.of("counts", List.of(2L, 1L)),
                Codecs.encode(loader, "demo.Out", apply(loader, "CountAll", in)));
    }

    @Test
    void aLambdaParameterOpensARecordsFields() throws Exception {
        BytesClassLoader loader = load("""
                module demo
                import List ( map )
                data Line = { sku: String, qty: Int }
                data In = { lines: List<Line> }
                data Out = { qtys: List<Int> }

                behavior quantities : (i: In) -> Out constructs Out
                let quantities (i) = Out { qtys = map(({ qty }) -> qty, i.lines) }
                """);

        Object in = Codecs.decoded(loader, "demo.In", java.util.Map.of("lines",
                List.of(java.util.Map.of("sku", "a", "qty", 2L),
                        java.util.Map.of("sku", "b", "qty", 5L))));
        assertEquals(java.util.Map.of("qtys", List.of(2L, 5L)),
                Codecs.encode(loader, "demo.Out", apply(loader, "Quantities", in)));
    }

    @Test
    void aBareParameterListStaysAParameterList() throws Exception {
        // `(a, b) -> e` is two parameters, not one tuple pattern (ADR-0036); a single tuple
        // parameter is written with its own parentheses, `((a, b)) -> e`
        BytesClassLoader loader = load("""
                module demo
                import List ( fold )
                data In = { xs: List<Int> }
                data Out = { total: Int }

                behavior total : (i: In) -> Out constructs Out
                let total (i) = Out { total = fold((acc, x) -> acc + x, 0, i.xs) }
                """);

        Object in = Codecs.decoded(loader, "demo.In", java.util.Map.of("xs", List.of(1L, 2L, 3L)));
        assertEquals(java.util.Map.of("total", 6L),
                Codecs.encode(loader, "demo.Out", apply(loader, "Total", in)));
    }

    @Test
    void aHelperParameterOpensANewtype() throws Exception {
        // the pattern names the type, so the parameter needs no annotation beside it
        BytesClassLoader loader = load("""
                module demo
                import List ( length )
                data Tags = List<String>

                let count (Tags(xs)) = length(xs)

                behavior countTags : (t: Tags) -> Int
                let countTags (t) = count(t)
                """);

        assertEquals(2L, apply(loader, "CountTags",
                Codecs.decoded(loader, "demo.Tags", List.of("a", "b"))));
    }

    @Test
    void aHelperParameterOpensARecordItAnnotates() throws Exception {
        BytesClassLoader loader = load("""
                module demo
                data Line = { sku: String, qty: Int }
                data Out = { v: Int }

                let twice ({ qty }: Line) = qty * 2

                behavior run : (l: Line) -> Out constructs Out
                let run (l) = Out { v = twice(l) }
                """);

        assertEquals(java.util.Map.of("v", 6L), Codecs.encode(loader, "demo.Out",
                apply(loader, "Run", Codecs.decoded(loader, "demo.Line",
                        java.util.Map.of("sku", "s-1", "qty", 3L)))));
    }

    @Test
    void openingSomethingThatIsNotANewtypeIsRejected() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Line = { sku: String, qty: Int }
                data Out = { v: String }

                behavior read : (l: Line) -> Out constructs Out
                let read (l) = {
                    let Line(x) = l
                    Out { v = x }
                }
                """));
        assertEquals("check.open.notnewtype", e.diagnostic().messageKey(), e.getMessage());
    }

    @Test
    void openingANewtypeTheValueIsNotIsRejected() {
        // outside a `match` nothing else establishes what the value is, so the name the pattern
        // writes is held against the value's own type
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Tags = List<String>
                data Labels = List<String>
                data Out = { v: Int }

                behavior read : (t: Tags) -> Out constructs Out
                let read (t) = {
                    let Labels(xs) = t
                    Out { v = 1 }
                }
                """));
        assertEquals("check.open.mismatch", e.diagnostic().messageKey(), e.getMessage());
    }

    @Test
    void openingASumsCaseIsRejectedAndPointsAtMatch() {
        // a case is refutable: the value may be the other one, and a binding has no second arm
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Paid
                data Unpaid
                data Status = Paid | Unpaid
                data Out = { v: Int }

                behavior read : (s: Status) -> Out constructs Out
                let read (s) = {
                    let Paid(x) = s
                    Out { v = 1 }
                }
                """));
        assertEquals("check.open.notnewtype", e.diagnostic().messageKey(), e.getMessage());
        assertTrue(e.getMessage().contains("match") || e.diagnostic().notes().toString().contains("match"),
                "the report points at `match`: " + e.getMessage());
    }

    @Test
    void aRefutablePatternIsRejectedInALambdaParameterToo() {
        // the same judgement, wherever the pattern is written
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                import List ( map )
                data Paid
                data Unpaid
                data Status = Paid | Unpaid
                data In = { ss: List<Status> }
                data Out = { v: List<Int> }

                behavior run : (i: In) -> Out constructs Out
                let run (i) = Out { v = map((Paid(x)) -> 1, i.ss) }
                """));
        assertEquals("check.open.notnewtype", e.diagnostic().messageKey(), e.getMessage());
    }

    @Test
    void openingSomeIsRejected() {
        // Option's cases are refutable too — `Some` is exactly the value that may be absent
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Line = { note: String? }
                data Out = { v: String }

                behavior read : (l: Line) -> Out constructs Out
                let read (l) = {
                    let Some(s) = l.note
                    Out { v = s }
                }
                """));
        assertEquals("check.open.notnewtype", e.diagnostic().messageKey(), e.getMessage());
    }
}
