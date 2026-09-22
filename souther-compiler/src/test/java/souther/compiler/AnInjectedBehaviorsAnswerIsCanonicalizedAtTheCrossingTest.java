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
 * An injected behavior's implementation is Java, supplied from outside the compiler — exactly as
 * foreign as a decoder's input, and answering just as freely with text that has left NFC. ADR-0096
 * named a derived decoder's string leaf and a source literal as the two doors text arrives through;
 * a required behavior's bare {@code String} answer is a third one it did not name, and
 * {@code BodyGen.requiredCall} (ADR-0120) canonicalizes it at the crossing the same way.
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
