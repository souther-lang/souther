package souther.compiler;

import javax.tools.ToolProvider;
import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;

/**
 * Compiles a hand-written Java class against a module's generated classes — how a Java or Kotlin
 * implementation of an injection target reaches the generated base (spec 13.3). A test that needs one
 * gets the real thing: javac reads the same class files a consuming build would, so a base whose
 * {@code apply} changed shape fails here as it would there.
 */
final class Subclasses {

    private Subclasses() {}

    /** The bytes of {@code className}, compiled from {@code source} with {@code generated} on the
     * classpath. */
    static byte[] compile(Map<String, byte[]> generated, String className, String source)
            throws Exception {
        Path classesDir = Files.createTempDirectory("souther-gen");
        for (Map.Entry<String, byte[]> e : generated.entrySet()) {
            Path p = classesDir.resolve(e.getKey().replace('.', '/') + ".class");
            Files.createDirectories(p.getParent());
            Files.write(p, e.getValue());
        }
        Path srcFile = classesDir.resolve(className.replace('.', '/') + ".java");
        Files.createDirectories(srcFile.getParent());
        Files.writeString(srcFile, source);
        Path outDir = Files.createTempDirectory("souther-impl");
        String cp = classesDir + File.pathSeparator + System.getProperty("java.class.path");
        int rc = ToolProvider.getSystemJavaCompiler().run(null, null, null,
                "-encoding", "UTF-8", "-classpath", cp, "-d", outDir.toString(), srcFile.toString());
        if (rc != 0) {
            throw new IllegalStateException("javac failed for " + className + " (rc=" + rc + ")");
        }
        return Files.readAllBytes(outDir.resolve(className.replace('.', '/') + ".class"));
    }
}
