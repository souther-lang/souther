package souther.compiler;

import souther.compiler.jvm.ClassFileImage;

import org.junit.jupiter.api.Test;

import javax.tools.ToolProvider;

import java.io.File;
import java.nio.file.Files;
import java.util.HashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

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
