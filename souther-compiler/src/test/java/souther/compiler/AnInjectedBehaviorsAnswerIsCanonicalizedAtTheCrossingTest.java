package souther.compiler;

import souther.compiler.jvm.ClassFileImage;

import org.junit.jupiter.api.Test;

import javax.tools.ToolProvider;

import java.io.File;
import java.nio.file.Files;
import java.util.HashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every place Java crosses into a Souther value that the boundary's original two doors (a derived
 * decoder's leaf, a source literal) did not name: an injected behavior's answer, a generated
 * behavior's public {@code apply} called directly, and — recursively — a {@code List} one of them
 * answers with. {@code CanonicalizeAtCrossing} closes all three the same way a decoder's leaf does,
 * and does it before an {@code ensures} check that cannot be proven statically ever reads the value.
 */
class AnInjectedBehaviorsAnswerIsCanonicalizedAtTheCrossingTest {

    private static final String MODULE = """
            module demo

            data Out = { v: String }

            behavior source : () -> String

            behavior run : (unused: Bool) -> Out constructs Out
                depends on source

            let run (unused, source) = Out { v = source() }
            """;

    private static final String IMPL_SRC = """
            package demo;
            public final class SourceImpl extends Source {
                public String apply() {
                    // "a" followed by a bare combining circumflex (U+0302) — decomposed, and never
                    // run through Strings.append, unlike anything this compiler would itself build.
                    return "a" + java.lang.Character.toString(0x0302);
                }
            }
            """;

    /** {@code "a"} composed with a combining circumflex — U+00E2, one code point — what the
     *  decomposed answer {@code IMPL_SRC} returns is NFC to. */
    private static final String A_CIRCUMFLEX = new String(Character.toChars(0x00E2));

    @Test
    void aRequiredBehaviorsBareStringAnswerArrivesComposed() throws Exception {
        Map<String, ClassFileImage> classes = new HashMap<>(Compiler.compile(MODULE));
        classes.put("demo.SourceImpl", compileSubclass(classes, "demo.SourceImpl", IMPL_SRC));

        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Class<?> source = loader.loadClass("demo.Source");
        Object impl = loader.loadClass("demo.SourceImpl").getConstructor().newInstance();
        Object run = loader.loadClass("demo.Run").getMethod("bind", source).invoke(null, impl);

        Object out = Codecs.apply(run, true);

        assertEquals(A_CIRCUMFLEX, ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("v"));
    }

    private static final String MODULE_WITH_ENSURES = """
            module demo

            data Out = { v: String }

            behavior source : (seed: Bool) -> String
                ensures (seed || Bool.not(seed)) && String.length(value) == 1

            behavior run : (unused: Bool) -> Out constructs Out
                depends on source

            let run (unused, source) = Out { v = source(unused) }
            """;

    private static final String IMPL_SRC_WITH_SEED = """
            package demo;
            public final class SourceImpl extends Source {
                public String apply(Boolean seed) {
                    return "a" + java.lang.Character.toString(0x0302);
                }
            }
            """;

    /**
     * The {@code ensures} check runs at the crossing (it cannot be proven statically — the
     * implementation is Java), so it has to see the canonicalized answer, not the two code points
     * {@code IMPL_SRC_WITH_SEED} actually returns. Before {@code CanonicalizeAtCrossing} ran ahead
     * of {@code checkAtCrossing} rather than after it, this same module raised an
     * {@code EnsuresFailure} on a value the carrier invariant says is one code point.
     */
    @Test
    void theRuntimeEnsuresCheckSeesTheCanonicalAnswerNotTheRawOne() throws Exception {
        Map<String, ClassFileImage> classes = new HashMap<>(Compiler.compile(MODULE_WITH_ENSURES));
        classes.put("demo.SourceImpl", compileSubclass(classes, "demo.SourceImpl", IMPL_SRC_WITH_SEED));

        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Class<?> source = loader.loadClass("demo.Source");
        Object impl = loader.loadClass("demo.SourceImpl").getConstructor().newInstance();
        Object run = loader.loadClass("demo.Run").getMethod("bind", source).invoke(null, impl);

        Object out = Codecs.apply(run, true);

        assertEquals(A_CIRCUMFLEX, ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("v"));
    }

    private static final String IDENTITY_MODULE = """
            module demo

            behavior identity : (s: String) -> String
            let identity (s) = s
            """;

    /**
     * A generated behavior's {@code apply} is public — a Java caller reaches it directly, not only
     * through another generated class — so a decomposed {@code String} handed in that way is a
     * crossing exactly as foreign as a decoder's input or an injected behavior's answer, and
     * {@code Backend.generateSpecFn} canonicalizes it before the body ({@code let identity (s) = s})
     * ever sees {@code s}.
     */
    @Test
    void aJavaCallersArgumentToAGeneratedBehaviorArrivesComposed() throws Exception {
        Map<String, ClassFileImage> classes = Compiler.compile(IDENTITY_MODULE);
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Object identity = Emitted.behavior(loader, "demo", "identity").getConstructor().newInstance();

        String decomposed = "a" + new String(Character.toChars(0x0302));
        Object answer = Codecs.apply(identity, decomposed);

        assertEquals(A_CIRCUMFLEX, answer);
    }

    private static final String LIST_MODULE = """
            module demo

            data Out = { names: List<String> }

            behavior source : () -> List<String>

            behavior run : (unused: Bool) -> Out constructs Out
                depends on source

            let run (unused, source) = Out { names = source() }
            """;

    private static final String LIST_IMPL_SRC = """
            package demo;
            import java.util.List;
            public final class SourceImpl extends Source {
                public List<String> apply() {
                    return List.of("a" + java.lang.Character.toString(0x0302));
                }
            }
            """;

    /**
     * A required behavior answering {@code List<String>} crosses the same door a bare {@code String}
     * does, and {@code CanonicalizeAtCrossing} recurses into the list's elements the same way
     * {@code CodecGen}'s encoder side already recurses into a nested container, rather than leaving
     * this shape as a documented but uncanonicalized exception to the carrier invariant.
     */
    @Test
    void aRequiredBehaviorsListOfStringAnswerArrivesComposed() throws Exception {
        Map<String, ClassFileImage> classes = new HashMap<>(Compiler.compile(LIST_MODULE));
        classes.put("demo.SourceImpl", compileSubclass(classes, "demo.SourceImpl", LIST_IMPL_SRC));

        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Class<?> source = loader.loadClass("demo.Source");
        Object impl = loader.loadClass("demo.SourceImpl").getConstructor().newInstance();
        Object run = loader.loadClass("demo.Run").getMethod("bind", source).invoke(null, impl);

        Object out = Codecs.apply(run, true);

        assertEquals(java.util.List.of(A_CIRCUMFLEX),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("names"));
    }

    private static final String LIST_OF_MAP_MODULE = """
            module demo

            data Out = { rows: List<Map<String, String>> }

            behavior source : () -> List<Map<String, String>>

            behavior run : (unused: Bool) -> Out constructs Out
                depends on source

            let run (unused, source) = Out { rows = source() }
            """;

    private static final String LIST_OF_MAP_IMPL_SRC = """
            package demo;
            import java.util.List;
            import java.util.Map;
            public final class SourceImpl extends Source {
                public List<Map<String, String>> apply() {
                    return List.of(Map.of("k", "a" + java.lang.Character.toString(0x0302)));
                }
            }
            """;

    /**
     * {@code List<Map<String, String>>} is a {@code Map} nested inside another container — the
     * shape {@code CanonicalizeAtCrossing.emitAsFunction} used to refuse outright with an
     * {@code IllegalArgumentException} for any {@code Map} reached as a container's element,
     * turning a valid declaration into a compiler crash rather than a documented gap. It now
     * composes the {@code Map}'s own key and value functions the same way {@code Lists}/{@code Sets}
     * /{@code Options} already compose one.
     */
    @Test
    void aListOfMapOfStringDoesNotCrashCodegenAndArrivesComposed() throws Exception {
        Map<String, ClassFileImage> classes = new HashMap<>(Compiler.compile(LIST_OF_MAP_MODULE));
        classes.put("demo.SourceImpl", compileSubclass(classes, "demo.SourceImpl", LIST_OF_MAP_IMPL_SRC));

        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Class<?> source = loader.loadClass("demo.Source");
        Object impl = loader.loadClass("demo.SourceImpl").getConstructor().newInstance();
        Object run = loader.loadClass("demo.Run").getMethod("bind", source).invoke(null, impl);

        Object out = Codecs.apply(run, true);

        Object rows = ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("rows");
        assertEquals(java.util.List.of(Map.of("k", A_CIRCUMFLEX)), rows);
    }

    private static final String PIPELINE_MODULE = """
            module demo

            data Out = Int

            behavior source : (seed: Bool) -> String
            behavior consume : (s: String) -> Out constructs Out
            let consume (s) = Out(String.length(s))

            behavior flow = source >-> consume
            """;

    /**
     * A pipeline's own public {@code apply} is exactly as reachable from Java as
     * {@code Backend.generateSpecFn}'s, and an injected stage's answer crosses into the next stage
     * the same way an injected behavior's answer crosses into a body that calls it — neither was
     * canonicalized: {@code generatePipe} never called {@code CanonicalizeAtCrossing} at all before
     * this fix, so {@code consume} read the two code points {@code source}'s Java implementation
     * actually returned.
     */
    @Test
    void aPipelinesInjectedStageOutputArrivesComposedAtTheNextStage() throws Exception {
        Map<String, ClassFileImage> classes = new HashMap<>(Compiler.compile(PIPELINE_MODULE));
        classes.put("demo.SourceImpl", compileSubclass(classes, "demo.SourceImpl", IMPL_SRC_WITH_SEED));

        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Class<?> source = loader.loadClass("demo.Source");
        Object impl = loader.loadClass("demo.SourceImpl").getConstructor().newInstance();
        Object flow = loader.loadClass("demo.Flow").getMethod("bind", source).invoke(null, impl);

        Object out = Codecs.apply(flow, true);

        assertEquals(1L, Codecs.encode(loader, "demo.Out", out));
    }

    private static final String ENSURES_ON_INPUT_MODULE = """
            module demo

            data Out = { len: Int, alsoOk: Bool }

            behavior echoLen : (s: String) -> Out constructs Out
                ensures value == value && String.length(s) == 1

            let echoLen (s) = Out { len = 99, alsoOk = true }
            """;

    /**
     * A generated behavior's own {@code ensures} runs against the same argument slots
     * {@code apply$body} reads, but {@code emitCheckingApply}'s wrapper used to reload the raw,
     * pre-canonicalization argument for the check while the body's own binding loop (already fixed)
     * saw the canonical one — the same asymmetry the output side had, now on the input side. The
     * body here computes something unrelated to {@code s}'s length, so the checker cannot prove the
     * relation statically and has to check it at the crossing.
     */
    @Test
    void theRuntimeEnsuresCheckSeesTheCanonicalArgumentNotTheRawOne() throws Exception {
        Map<String, ClassFileImage> classes = Compiler.compile(ENSURES_ON_INPUT_MODULE);
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Object echoLen = Emitted.behavior(loader, "demo", "echoLen").getConstructor().newInstance();

        String decomposed = "a" + new String(Character.toChars(0x0302));
        Object out = Codecs.apply(echoLen, decomposed);

        assertEquals(99L, ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("len"));
    }

    private static final String UNION_MODULE = """
            module demo

            data Missing

            behavior source : (seed: Bool) -> String | Missing

            behavior run : (unused: Bool) -> String
                depends on source

            let run (unused, source) = match source(unused) with
                | String as s -> s
                | Missing -> "?"
            """;

    private static final String UNION_IMPL_SRC = """
            package demo;
            public final class SourceImpl extends Source {
                public SourceResult apply(Boolean seed) {
                    // String is bridged (a primitive belongs to no module), so a Java answer of the
                    // String arm is this generated wrapper record, not a bare String.
                    return new StringCase("a" + java.lang.Character.toString(0x0302));
                }
            }
            """;

    /**
     * {@code String | Missing} is a real, existing shape (spec has {@code Member | Missing}ーlike
     * unions), and {@code CanonicalizeAtCrossing} used to read any {@code Type.Union} as
     * structurally not reaching {@code String} and do nothing — a Java implementation answering the
     * {@code String} arm crossed uncanonicalized. Which arm a crossing value actually is is not
     * known until run time, so this is the one case checked with a runtime {@code instanceof}
     * rather than settled at codegen time the way every other shape is.
     */
    @Test
    void aRequiredBehaviorsUnionWithABareStringMemberArrivesComposed() throws Exception {
        Map<String, ClassFileImage> classes = new HashMap<>(Compiler.compile(UNION_MODULE));
        classes.put("demo.SourceImpl", compileSubclass(classes, "demo.SourceImpl", UNION_IMPL_SRC));

        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Class<?> source = loader.loadClass("demo.Source");
        Object impl = loader.loadClass("demo.SourceImpl").getConstructor().newInstance();
        Object run = loader.loadClass("demo.Run").getMethod("bind", source).invoke(null, impl);

        Object out = Codecs.apply(run, true);

        assertEquals(A_CIRCUMFLEX, out);
    }

    private static final String MAP_COLLISION_MODULE = """
            module demo

            data Out = { m: Map<String, Int> }

            behavior source : () -> Map<String, Int>

            behavior run : (unused: Bool) -> Out constructs Out
                depends on source

            let run (unused, source) = Out { m = source() }
            """;

    private static final String MAP_COLLISION_IMPL_SRC = """
            package demo;
            import java.util.LinkedHashMap;
            import java.util.Map;
            public final class SourceImpl extends Source {
                public Map<String, Long> apply() {
                    // Two distinct keys the crossing's own canonicalization collapses into one —
                    // "a\\u0302" and the precomposed "\\u00e2" — each with a different value.
                    Map<String, Long> m = new LinkedHashMap<>();
                    m.put("a" + java.lang.Character.toString(0x0302), 1L);
                    m.put(java.lang.Character.toString(0x00e2), 2L);
                    return m;
                }
            }
            """;

    /**
     * A canonicalization collision on a {@code Map}'s key drops an entry silently unless it is
     * refused, the same reason a derived decoder refuses one as {@code duplicate_key} rather than
     * picking a survivor. {@code Maps.canonicalizeWith} aborts instead of overwriting, which
     * {@link souther.runtime.ConstraintViolation} carries — a defect in the crossing's own data,
     * not a business result the domain should have to model.
     */
    @Test
    void aMapKeyCanonicalizationCollisionAbortsRatherThanSilentlyOverwriting() throws Exception {
        Map<String, ClassFileImage> classes = new HashMap<>(Compiler.compile(MAP_COLLISION_MODULE));
        classes.put("demo.SourceImpl", compileSubclass(classes, "demo.SourceImpl", MAP_COLLISION_IMPL_SRC));

        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Class<?> source = loader.loadClass("demo.Source");
        Object impl = loader.loadClass("demo.SourceImpl").getConstructor().newInstance();
        Object run = loader.loadClass("demo.Run").getMethod("bind", source).invoke(null, impl);

        org.junit.jupiter.api.function.Executable call = () -> Codecs.apply(run, true);
        org.junit.jupiter.api.Assertions.assertThrows(
                souther.runtime.ConstraintViolation.class, call);
    }

    private static final String RAW_CONSTRUCTION_MODULE = """
            module demo

            data Name = { text: String }

            behavior source : () -> Name

            behavior run : (unused: Bool) -> Name
                depends on source

            let run (unused, source) = source()
            """;

    private static final String RAW_CONSTRUCTION_IMPL_SRC = """
            package demo;
            public final class SourceImpl extends Source {
                public Name apply() {
                    // Same-package Java calling the canonical constructor directly, not through
                    // __construct or the protected factory — ADR-0065 lets raw record construction
                    // exist, and the package-private constructor does not refuse a same-package
                    // caller for having skipped either of those two doors.
                    return new Name("a" + java.lang.Character.toString(0x0302));
                }
            }
            """;

    /**
     * A data's canonical constructor is package-private, not sealed off from Java: an injected
     * behavior's implementation shares the package and can write {@code new Name(...)} directly,
     * bypassing both {@code __construct} (which runs the invariant) and the {@code protected}
     * factory ({@code Backend.emitDataFactory}, which already canonicalized before this fix). Before
     * {@code emitCtor} canonicalized each field itself, this was a real hole in the carrier
     * invariant: a decomposed field value could reach Souther code with no crossing having read it.
     */
    @Test
    void aSamePackageJavasRawConstructionOfADataArrivesComposed() throws Exception {
        Map<String, ClassFileImage> classes = new HashMap<>(Compiler.compile(RAW_CONSTRUCTION_MODULE));
        classes.put("demo.SourceImpl", compileSubclass(classes, "demo.SourceImpl", RAW_CONSTRUCTION_IMPL_SRC));

        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Class<?> source = loader.loadClass("demo.Source");
        Object impl = loader.loadClass("demo.SourceImpl").getConstructor().newInstance();
        Object run = loader.loadClass("demo.Run").getMethod("bind", source).invoke(null, impl);

        Object out = Codecs.apply(run, true);

        assertEquals(A_CIRCUMFLEX, ((Map<?, ?>) Codecs.encode(loader, "demo.Name", out)).get("text"));
    }

    private static final String CONSTRUCT_CROSSING_MODULE = """
            module demo

            data Name = { text: String } invariant String.length(text) == 1
            """;

    /**
     * {@code __construct} is public whenever another module may call it directly (ADR-0002), so it
     * is a crossing in its own right, not only reachable through the canonicalizing factory this
     * module's own behaviors go through. Before the invariant's own argument slots were
     * canonicalized ahead of {@code bindFields}, a decomposed argument here would fail the
     * {@code invariant} clause on a length the carrier invariant already says is wrong to count.
     */
    @Test
    void constructSeesTheCanonicalArgumentWhenCalledDirectlyAcrossAModule() throws Exception {
        Map<String, ClassFileImage> classes = Compiler.compile(CONSTRUCT_CROSSING_MODULE);
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Class<?> nameClass = loader.loadClass("demo.Name");

        String decomposed = "a" + new String(Character.toChars(0x0302));
        Object result = nameClass.getMethod("__construct", String.class).invoke(null, decomposed);

        assertTrue(result instanceof souther.runtime.Result.Ok<?, ?>);
        Object ok = ((souther.runtime.Result.Ok<?, ?>) result).value();
        assertEquals(A_CIRCUMFLEX, ((Map<?, ?>) Codecs.encode(loader, "demo.Name", ok)).get("text"));
    }

    private static ClassFileImage compileSubclass(Map<String, ClassFileImage> generated,
                                                    String className, String source)
            throws Exception {
        java.nio.file.Path classesDir = Files.createTempDirectory("souther-gen");
        for (Map.Entry<String, ClassFileImage> e : generated.entrySet()) {
            java.nio.file.Path p = classesDir.resolve(e.getKey().replace('.', '/') + ".class");
            Files.createDirectories(p.getParent());
            Files.write(p, e.getValue().bytes());
        }
        java.nio.file.Path srcFile = classesDir.resolve(className.replace('.', '/') + ".java");
        Files.writeString(srcFile, source);
        java.nio.file.Path outDir = Files.createTempDirectory("souther-impl");
        String cp = classesDir + File.pathSeparator + System.getProperty("java.class.path");
        int rc = ToolProvider.getSystemJavaCompiler().run(null, null, null,
                "-encoding", "UTF-8", "-classpath", cp, "-d", outDir.toString(), srcFile.toString());
        if (rc != 0) {
            throw new IllegalStateException("javac failed for " + className + " (rc=" + rc + ")");
        }
        return ClassFileImage.of(
                Files.readAllBytes(outDir.resolve(className.replace('.', '/') + ".class")));
    }
}
