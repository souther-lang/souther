package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Giving a {@code ?} field a value from a behavior body (spec §algebraic-types): a plain value is wrapped in
 * {@code Some}, and {@code None} is the empty one. Both are construction — the one place an optional
 * is made — so the type is still never named and {@code Some(...)} is still not a call anyone can
 * write (ADR-0011, issue #167). {@link OptionalFieldReadsAWrittenNullTest} covers the codec side of the same
 * field.
 */
class CompileOptionalFieldConstructionTest {

    private static final String MODULE = """
            module demo

            data Note = String
            data In = { id: String, n: Note, keep: Bool }
            data Out = { id: String, note: Note? }

            behavior run : (i: In) -> Out constructs Out

            let run (i) = %s
            """;

    private Map<?, ?> run(String body) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(
                Compiler.compile(MODULE.formatted(body)), getClass().getClassLoader());
        Map<String, Object> input = new HashMap<>();
        input.put("id", "x-1");
        input.put("n", "hello");
        input.put("keep", true);
        Object in = Codecs.decoded(loader, "demo.In", input);
        Object behavior = Emitted.behavior(loader, "demo", "run").getConstructor().newInstance();
        return (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
    }

    @Test
    void aPlainValueIsWrapped() throws Exception {
        assertEquals("hello", run("Out { id = i.id, note = i.n }").get("note"));
    }

    @Test
    void aConstructedValueIsWrapped() throws Exception {
        // The value need not be read from somewhere: a newtype built here wraps the same way.
        String src = """
                module demo

                data Note = String
                data In = { id: String }
                data Out = { id: String, note: Note? }

                behavior run : (i: In) -> Out constructs Out, Note

                let run (i) = Out { id = i.id, note = Note("fresh") }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In", Map.of("id", "x-1"));
        Object behavior = Emitted.behavior(loader, "demo", "run").getConstructor().newInstance();
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
        assertEquals("fresh", out.get("note"));
    }

    @Test
    void noneIsTheEmptyOne() throws Exception {
        Map<?, ?> out = run("Out { id = i.id, note = None }");
        assertFalse(out.containsKey("note"), "an empty optional encodes to no key at all: " + out);
    }

    @Test
    void anOptionalReadElsewhereStillPassesThrough() throws Exception {
        // The form that already worked: the value is an optional to begin with, so nothing wraps it.
        String src = """
                module demo

                data Note = String
                data In = { id: String, note: Note? }
                data Out = { id: String, note: Note? }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { id = i.id, note = i.note }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In", Map.of("id", "x-1", "note", "kept"));
        Object behavior = Emitted.behavior(loader, "demo", "run").getConstructor().newInstance();
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
        assertEquals("kept", out.get("note"));
    }

    @Test
    void aConditionalGivesTheFieldEitherOne() throws Exception {
        // The shape the trick existed for: present or absent by a rule. Each branch is lifted before
        // the two are joined, so the `if` has one type without either side naming it.
        assertEquals("hello", run("Out { id = i.id, note = if i.keep then i.n else None }").get("note"));
        Map<?, ?> dropped = run("Out { id = i.id, note = if i.keep then None else i.n }");
        assertFalse(dropped.containsKey("note"), dropped.toString());
    }

    @Test
    void aMatchArmGivesTheFieldEitherOne() throws Exception {
        String src = """
                module demo

                data Note = String
                data Present = { n: Note }
                data Which = Absent | Present
                data In = { id: String, which: Which }
                data Out = { id: String, note: Note? }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { id = i.id, note = match i.which with
                                                         | Present { n } -> n
                                                         | Absent        -> None }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object behavior = Emitted.behavior(loader, "demo", "run").getConstructor().newInstance();

        Object present = Codecs.decoded(loader, "demo.In", Map.of("id", "x-1",
                "which", Map.of("type", "Present", "n", "here")));
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, present));
        assertEquals("here", out.get("note"));

        Object absent = Codecs.decoded(loader, "demo.In", Map.of("id", "x-2",
                "which", Map.of("type", "Absent")));
        Map<?, ?> gone = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, absent));
        assertFalse(gone.containsKey("note"), gone.toString());
    }

    @Test
    void aStepForFilterMapStillHasToAnswerAnOptionalOfItsOwn() {
        // The lift reaches branches, but only under a field: a lambda is typed with no expected type,
        // so absence the model owns still does not become an optional here (issue #166).
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                import List ( filterMap )

                data Note = String
                data Issue = { id: String, n: Note, keep: Bool }
                data In = { issues: List<Issue> }
                data Out = { notes: List<Note> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { notes = filterMap(x -> if x.keep then x.n else None, i.issues) }
                """));
        assertTrue(e.getMessage().contains("None") || e.getMessage().contains("filterMap"),
                e.getMessage());
    }

    @Test
    void noneOutsideAnOptionalFieldIsStillRejected() {
        // The wrap is a construction rule, not a coercion: `None` means nothing where the field is
        // not optional, and nothing where there is no field at all.
        CompileException onField = assertThrows(CompileException.class,
                () -> Compiler.compile(MODULE.formatted("Out { id = None, note = None }")));
        assertEquals("E1303", onField.code(), onField.getMessage());

        CompileException bare = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Note = String
                data Out = { note: Note? }
                behavior run : (o: Out) -> Out
                let run (o) = None
                """));
        assertEquals("E1303", bare.code(), bare.getMessage());
    }

    @Test
    void someIsStillNotACallAnyoneCanWrite() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile(MODULE.formatted("Out { id = i.id, note = Some(i.n) }")));
        assertEquals("E1303", e.code(), e.getMessage());
    }

    @Test
    void aWrongTypeIsStillAWrongType() {
        // The wrap is over the field's own element type; anything else is the mismatch it was.
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile(MODULE.formatted("Out { id = i.id, note = i.id }")));
        assertTrue(e.getMessage().contains("note"), e.getMessage());
    }
}
