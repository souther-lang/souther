package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.runtime.Behavior;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Modifier;
import java.util.HashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An injected behavior (a {@code behavior} with no {@code let}) may take more than one input, like a
 * fn behavior. Declaring 2+ params and calling with all of them type-checks; calling with the wrong
 * count is an arity error rather than a silent drop of the extra arguments (issue #57).
 */
class CompileInjectedMultiArgTest {

    private static final String HEAD = """
            module demo

            data A = { x: Int }
            data B = { y: Int }
            data R = { z: Int }

            behavior send : (a: A, b: B) -> R
                constructs R

            behavior use : (a: A, b: B) -> R
                depends on send

            """;

    @Test
    void aTwoArgInjectedCallTypechecks() {
        // the natural call send(a, b) must type-check — today it errors "expects 1 argument, got 2"
        String src = HEAD + "let use (a, b, send) = send(a, b)\n";
        Compiler.compile(src);   // throws today; must not after the fix
    }

    @Test
    void callingATwoArgInjectedWithOneArgIsAnArityError() {
        // the silent-drop hole: send(a) on a 2-input spec used to compile, dropping b
        String src = HEAD + "let use (a, b, send) = send(a)\n";
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertTrue(e.getMessage().contains("send") || e.getMessage().toLowerCase().contains("argument"),
                e.getMessage());
    }

    @Test
    void aTwoArgInjectedBaseIsAStandaloneAbstractClassWithTypedApply() throws Exception {
        // 2+ inputs → standalone abstract class, no Behavior supertype (so it cannot follow an
        // arrow), typed apply(A,B)
        String src = HEAD + "let use (a, b, send) = send(a, b)\n";
        Map<String, byte[]> classes = Compiler.compile(src);
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Class<?> send = loader.loadClass("demo.Send");
        assertTrue(Modifier.isAbstract(send.getModifiers()), "the injected base is abstract");
        assertFalse(Behavior.class.isAssignableFrom(send),
                "a multi-input injected behavior does not implement the unary Behavior contract");
        Class<?> a = loader.loadClass("demo.A");
        Class<?> b = loader.loadClass("demo.B");
        assertNotNull(send.getMethod("apply", a, b), "declares a typed apply(A, B)");
    }

    @Test
    void aTwoArgInjectedBaseWithAUnionOutputGetsItsResultInterface() throws Exception {
        // the base's apply returns `<名>Result`, so that interface has to be generated here — a
        // multi-input injected behavior used to be skipped, leaving the base pointing at a class
        // that never existed (issue #96)
        String src = """
                module demo
                data A = { x: Int }
                data B = { y: Int }
                data Ok = { z: Int }
                data Rejected = { why: String }
                behavior send : (a: A, b: B) -> Ok | Rejected
                """;
        Map<String, byte[]> classes = Compiler.compile(src);
        assertTrue(classes.containsKey(Emitted.result("demo", "send")),
                "the union output's sealed interface is generated: " + classes.keySet());
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Class<?> send = loader.loadClass("demo.Send");
        assertEquals(loader.loadClass(Emitted.result("demo", "send")),
                send.getMethod("apply", loader.loadClass("demo.A"), loader.loadClass("demo.B"))
                        .getReturnType());
    }

    @Test
    void aZeroArgInjectedBaseWithAUnionOutputGetsItsResultInterface() {
        String src = """
                module demo
                data Ok = { z: Int }
                data Rejected = { why: String }
                behavior now : () -> Ok | Rejected
                """;
        assertTrue(Compiler.compile(src).containsKey(Emitted.result("demo", "now")),
                "a zero-input injected behavior's union output needs the same interface");
    }

    @Test
    void aTwoArgInjectedBehaviorStartsAPipelineAndRuns() throws Exception {
        // `>->` hands a single value along, so a multi-input behavior cannot follow an arrow — but the first
        // stage receives the pipeline's own arguments, so any number is fine there, injected or implemented
        // (spec §sequential-composition). The stage is read from the pipeline's injected field and called on
        // its base class with the typed apply (issue #96).
        String src = """
                module demo

                data A = { x: Int }
                data B = { y: Int }
                data R = { z: Int }

                behavior send : (a: A, b: B) -> R
                    constructs R

                behavior bump : (r: R) -> R
                    constructs R
                let bump (r) = R { z = r.z + 1 }

                behavior pipe = send >-> bump
                """;
        Map<String, byte[]> classes = new HashMap<>(Compiler.compile(src));
        classes.put("demo.SendImpl", Subclasses.compile(classes, "demo.SendImpl", IMPL_SRC));
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());

        Object pipe = loader.loadClass("demo.Pipe").getMethod("bind", loader.loadClass("demo.Send"))
                .invoke(null, loader.loadClass("demo.SendImpl").getConstructor().newInstance());
        Object a = Codecs.decoded(loader, "demo.A", Map.of("x", 2L));
        Object b = Codecs.decoded(loader, "demo.B", Map.of("y", 40L));
        Object r = pipe.getClass().getMethod("apply", loader.loadClass("demo.A"), loader.loadClass("demo.B"))
                .invoke(pipe, a, b);

        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.R", r);
        assertEquals(43L, out.get("z"), "send(2, 40) = 42, bump +1");
    }

    @Test
    void aZeroArgInjectedBaseIsAStandaloneAbstractClassWithANoArgApply() throws Exception {
        // a `() -> R` produces; it does not transform. The unary Behavior has an input to hand over
        // and this has none, so it is a standalone base with `apply()` — the same branch 2+ inputs
        // take, and the same shape a `() -> R` fn behavior's interface already had.
        String src = """
                module demo
                data R = { z: Int }
                behavior now : () -> R
                """;
        Map<String, byte[]> classes = Compiler.compile(src);
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Class<?> now = loader.loadClass("demo.Now");
        assertTrue(Modifier.isAbstract(now.getModifiers()), "the injected base is abstract");
        assertFalse(Behavior.class.isAssignableFrom(now),
                "a producer has no input to receive, so it is not the unary Behavior");
        assertEquals(loader.loadClass("demo.R"), now.getMethod("apply").getReturnType(),
                "declares a typed apply()");
    }

    @Test
    void aZeroArgInjectedBehaviorStartsAPipelineAndRuns() throws Exception {
        // only a first stage can take other than one input (spec §sequential-composition); a producer is called on its
        // own base class, with nothing handed to it
        String src = """
                module demo
                data R = { z: Int }
                behavior now : () -> R
                    constructs R
                behavior bump : (r: R) -> R
                    constructs R
                let bump (r) = R { z = r.z + 1 }
                behavior pipe = now >-> bump
                """;
        String impl = """
                package demo;
                public final class NowImpl extends Now {
                    public R apply() { return R(41); }
                }
                """;
        Map<String, byte[]> classes = new HashMap<>(Compiler.compile(src));
        classes.put("demo.NowImpl", Subclasses.compile(classes, "demo.NowImpl", impl));
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Object pipe = loader.loadClass("demo.Pipe").getMethod("bind", loader.loadClass("demo.Now"))
                .invoke(null, loader.loadClass("demo.NowImpl").getConstructor().newInstance());
        Object r = pipe.getClass().getMethod("apply").invoke(pipe);

        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.R", r);
        assertEquals(42L, out.get("z"));
    }

    @Test
    void aBodyCallsAZeroArgInjectedDependencyWithNoArgument() throws Exception {
        // the other call site of a producer: a body's `now()`, read from the injected field and
        // called on the base class. Nothing is handed over, so nothing has to stand in for an input.
        String src = """
                module demo
                data R = { z: Int }
                behavior now : () -> R
                    constructs R
                behavior use : (r: R) -> R
                    depends on now
                    constructs R
                let use (r, now) = {
                    let n = now()
                    R { z = r.z + n.z }
                }
                """;
        String impl = """
                package demo;
                public final class NowImpl extends Now {
                    public R apply() { return R(40); }
                }
                """;
        Map<String, byte[]> classes = new HashMap<>(Compiler.compile(src));
        classes.put("demo.NowImpl", Subclasses.compile(classes, "demo.NowImpl", impl));
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());

        Object use = loader.loadClass("demo.Use").getMethod("bind", loader.loadClass("demo.Now"))
                .invoke(null, loader.loadClass("demo.NowImpl").getConstructor().newInstance());
        Object r = Codecs.apply(use, Codecs.decoded(loader, "demo.R", Map.of("z", 2L)));

        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.R", r);
        assertEquals(42L, out.get("z"));
    }

    @Test
    void aSingleArgInjectedBaseStillImplementsBehavior() throws Exception {
        // orthogonality: a 1-input injected behavior is unchanged — it still composes with >->
        String src = """
                module demo
                data A = { x: Int }
                data R = { z: Int }
                behavior one : (a: A) -> R
                behavior use : (a: A) -> R depends on one
                let use (a, one) = one(a)
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Class<?> one = loader.loadClass("demo.One");
        assertTrue(Behavior.class.isAssignableFrom(one), "a single-input injected base stays a Behavior");
    }

    @Test
    void aPipelineStageDependingOnAMultiArgInjectedLoadsAndRuns() throws Exception {
        // a `>->` stage whose body requires a multi-arg injected dep: the pipeline stores that dep as
        // its base class, so pushStage must read/wire it as the base class, not the unary Behavior
        String src = """
                module demo

                data A = { x: Int }
                data B = { y: Int }
                data R = { z: Int }
                data S = { w: Int }

                behavior send : (a: A, b: B) -> R
                    constructs R

                behavior stage1 : (s: S) -> R
                    constructs A, B
                    depends on send

                let stage1 (s, send) = send(A { x = s.w }, B { y = s.w })

                behavior stage2 : (r: R) -> R
                    constructs R

                let stage2 (r) = R { z = r.z + 1 }

                behavior pipe = stage1 >-> stage2
                """;
        String impl = """
                package demo;
                public final class SendImpl extends Send {
                    public R apply(A a, B b) { return R(a.x() + b.y()); }
                }
                """;
        Map<String, byte[]> classes = new HashMap<>(Compiler.compile(src));
        classes.put("demo.SendImpl", Subclasses.compile(classes, "demo.SendImpl", impl));
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());

        Object pipe = loader.loadClass("demo.Pipe").getMethod("bind", loader.loadClass("demo.Send"))
                .invoke(null, loader.loadClass("demo.SendImpl").getConstructor().newInstance());
        Object s = Codecs.decoded(loader, "demo.S", Map.of("w", 20L));
        Object r = Codecs.apply(pipe, s);   // send(A{20}, B{20}) = 40, stage2 +1 = 41
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.R", r);
        assertEquals(41L, out.get("z"));
    }

    private static final String IMPL_SRC = """
            package demo;
            public final class SendImpl extends Send {
                public R apply(A a, B b) {
                    return R(a.x() + b.y());   // inherited protected factory for `constructs R`
                }
            }
            """;

    @Test
    void aTwoArgInjectedIsBoundAndCalledWithBothArguments() throws Exception {
        String src = HEAD + "let use (a, b, send) = send(a, b)\n";
        Map<String, byte[]> classes = new HashMap<>(Compiler.compile(src));
        classes.put("demo.SendImpl", Subclasses.compile(classes, "demo.SendImpl", IMPL_SRC));
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());

        Class<?> send = loader.loadClass("demo.Send");
        Class<?> a = loader.loadClass("demo.A");
        Class<?> b = loader.loadClass("demo.B");
        Object useSvc = loader.loadClass("demo.Use").getMethod("bind", send)
                .invoke(null, loader.loadClass("demo.SendImpl").getConstructor().newInstance());

        Object aVal = Codecs.decoded(loader, "demo.A", Map.of("x", 2L));
        Object bVal = Codecs.decoded(loader, "demo.B", Map.of("y", 40L));
        Object r = useSvc.getClass().getMethod("apply", a, b).invoke(useSvc, aVal, bVal);

        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.R", r);
        assertEquals(42L, out.get("z"), "both arguments reach the Java implementation");
    }

    @Test
    void aMultiArgInjectedMixesAPrimitiveAndADataArgViaALetBinding() throws Exception {
        // exercises primitive boxing (Int -> Long) alongside a data ref, and the let-binding tail path
        String head = """
                module demo

                data A = { x: Int }
                data R = { z: Int }

                behavior scale : (n: Int, a: A) -> R
                    constructs R

                behavior use : (n: Int, a: A) -> R
                    depends on scale

                let use (n, a, scale) = {
                    let m = scale(n, a)
                    m
                }
                """;
        String impl = """
                package demo;
                public final class ScaleImpl extends Scale {
                    public R apply(Long n, A a) {
                        return R(n * a.x());
                    }
                }
                """;
        Map<String, byte[]> classes = new HashMap<>(Compiler.compile(head));
        classes.put("demo.ScaleImpl", Subclasses.compile(classes, "demo.ScaleImpl", impl));
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());

        Class<?> scale = loader.loadClass("demo.Scale");
        Object useSvc = loader.loadClass("demo.Use").getMethod("bind", scale)
                .invoke(null, loader.loadClass("demo.ScaleImpl").getConstructor().newInstance());
        Object aVal = Codecs.decoded(loader, "demo.A", Map.of("x", 14L));
        Object r = useSvc.getClass().getMethod("apply", Long.class, loader.loadClass("demo.A"))
                .invoke(useSvc, 3L, aVal);
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.R", r);
        assertEquals(42L, out.get("z"));
    }

    @Test
    void aMultiArgInjectedDependencyIsFakedByATupleTable() {
        // CTFE: an example may evaluate a behavior whose 2-arg dependency is faked by an input tuple
        String src = HEAD + """
                let use (a, b, send) = send(a, b)

                fake send
                  | (A { x = 1 }, B { y = 2 }) -> R { z = 3 }

                example use
                  | (A { x = 1 }, B { y = 2 }) -> R { z = 3 }
                """;
        assertDoesNotThrow(() -> Compiler.compile(src));
    }

    @Test
    void aMultiArgDependencyIsFakedByAConstantWith() {
        // a `with dep = value` constant fake must also work for a multi-arg dep (not only a table)
        String src = HEAD + """
                let use (a, b, send) = send(a, b)

                example use
                  | (A { x = 1 }, B { y = 2 }) with send = R { z = 7 } -> R { z = 7 }
                """;
        assertDoesNotThrow(() -> Compiler.compile(src));
    }

    @Test
    void aMultiArgFakeRowWithWrongInputCountIsReported() {
        // a fake row that writes fewer inputs than the dependency's arity is a diagnostic, not a crash
        String src = HEAD + """
                let use (a, b, send) = send(a, b)

                fake send
                  | (A { x = 1 }) -> R { z = 3 }

                example use
                  | (A { x = 1 }, B { y = 2 }) -> R { z = 3 }
                """;
        assertThrows(CompileException.class, () -> Compiler.compile(src));
    }

    @Test
    void aMultiArgFakeTupleMissIsReported() {
        String src = HEAD + """
                let use (a, b, send) = send(a, b)

                fake send
                  | (A { x = 1 }, B { y = 2 }) -> R { z = 3 }

                example use
                  | (A { x = 9 }, B { y = 2 }) -> R { z = 3 }
                """;
        assertThrows(CompileException.class, () -> Compiler.compile(src));
    }

    /** Compiles {@code source} against the generated classes and returns the class bytes. */
    @Test
    void callingATwoArgInjectedWithAWronglyTypedArgIsRejected() {
        // arg 2 must be type-checked against param b: B, not ignored
        String src = HEAD + "let use (a, b, send) = send(a, a)\n";
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertTrue(e.getMessage().contains("B") || e.getMessage().contains("A"), e.getMessage());
    }
}
