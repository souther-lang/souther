package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import javax.tools.JavaCompiler;
import javax.tools.ToolProvider;
import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.jar.JarEntry;
import java.util.jar.JarOutputStream;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Recovered documentation is worth having only because it is true of the member it is printed
 * against. Two ways of getting that wrong survive keying by name and parameter count: an overload
 * that is simply undocumented takes its namesake's, and a jar with no sources beside it takes
 * whatever the tool happens to carry for that name — which is another version of the library.
 */
class JavadocIsOnlyPrintedWhereItProvablyBelongsTest {

    private static Path jarOf(Path dir, String name, String... sources) throws Exception {
        JavaCompiler javac = ToolProvider.getSystemJavaCompiler();
        Path classes = Files.createDirectories(dir.resolve(name + "-classes"));
        String[] args = new String[sources.length + 2];
        args[0] = "-d";
        args[1] = classes.toString();
        System.arraycopy(sources, 0, args, 2, sources.length);
        assertEquals(0, javac.run(null, OutputStream.nullOutputStream(), OutputStream.nullOutputStream(), args));

        Path jar = dir.resolve(name + ".jar");
        try (JarOutputStream out = new JarOutputStream(Files.newOutputStream(jar))) {
            try (Stream<Path> files = Files.walk(classes)) {
                for (Path f : files.filter(Files::isRegularFile).toList()) {
                    out.putNextEntry(new JarEntry(classes.relativize(f).toString()));
                    out.write(Files.readAllBytes(f));
                }
            }
        }
        return jar;
    }

    private static String api(String name, Path classPath) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        assertEquals(0, JapiCommand.run(new String[]{name, "-cp", classPath.toString()},
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(OutputStream.nullOutputStream(), true, StandardCharsets.UTF_8)));
        return out.toString(StandardCharsets.UTF_8);
    }

    @Test
    void anUndocumentedOverloadDoesNotBorrowItsNamesakesParameterName() throws Exception {
        Path dir = Files.createTempDirectory("one-documented");
        Path src = dir.resolve("acme/Reader.java");
        Files.createDirectories(src.getParent());
        Files.writeString(src, """
                package acme;

                /** Reads things. */
                public final class Reader {

                    /**
                     * Reads from text.
                     *
                     * @param text the text to read
                     */
                    public String read(String text) {
                        return text;
                    }

                    public String read(byte[] bytes) {
                        return new String(bytes);
                    }
                }
                """);
        Path jar = jarOf(dir, "reader-1.0", src.toString());
        try (JarOutputStream out = new JarOutputStream(
                Files.newOutputStream(dir.resolve("reader-1.0-sources.jar")))) {
            out.putNextEntry(new JarEntry("acme/Reader.java"));
            out.write(Files.readAllBytes(src));
        }

        String api = api("acme.Reader", jar);

        assertTrue(api.contains("read(byte[] bytes)"),
                "the undocumented overload still names its parameter, because its declaration"
                        + " does:\n" + api);
        assertTrue(api.contains("read(String text)"),
                "while the documented one keeps what was written for it:\n" + api);
        int documented = api.indexOf("Reads from text.");
        assertTrue(documented >= 0 && documented < api.indexOf("read(String text)")
                        && api.indexOf("Reads from text.", api.indexOf("read(byte[] bytes)")) < 0,
                "and the sentence sits only above the overload it was written for:\n" + api);
    }

    @Test
    void twoTypesOfTheSameSimpleNameAreNotTheSameParameter() throws Exception {
        Path dir = Files.createTempDirectory("same-simple-name");
        Path a = dir.resolve("a/Foo.java");
        Path b = dir.resolve("b/Foo.java");
        Path use = dir.resolve("acme/Use.java");
        Files.createDirectories(a.getParent());
        Files.createDirectories(b.getParent());
        Files.createDirectories(use.getParent());
        Files.writeString(a, "package a;\npublic class Foo {}\n");
        Files.writeString(b, "package b;\npublic class Foo {}\n");
        Files.writeString(use, """
                package acme;

                /** Uses things. */
                public class Use {

                    /** Uses the one from a. */
                    public void use(a.Foo value) {
                    }

                    /** Uses the one from b. */
                    public void use(b.Foo value) {
                    }
                }
                """);
        Path jar = jarOf(dir, "use-1.0", a.toString(), b.toString(), use.toString());
        try (JarOutputStream out = new JarOutputStream(
                Files.newOutputStream(dir.resolve("use-1.0-sources.jar")))) {
            out.putNextEntry(new JarEntry("acme/Use.java"));
            out.write(Files.readAllBytes(use));
        }

        String api = api("acme.Use", jar);

        int fromA = api.indexOf("use(a.Foo value)");
        int fromB = api.indexOf("use(b.Foo value)");
        assertTrue(fromA >= 0 && fromB >= 0, api);
        int docA = api.indexOf("Uses the one from a.");
        int docB = api.indexOf("Uses the one from b.");
        assertTrue(docA >= 0 && docA < fromA && fromA < docB && docB < fromB,
                "each overload keeps the sentence written for its own parameter type:\n" + api);
    }

    @Test
    void parameterNamesComeFromTheDeclarationRatherThanTheOrderTheTagsWereWrittenIn() throws Exception {
        Path dir = Files.createTempDirectory("tag-order");
        Path src = dir.resolve("acme/Join.java");
        Files.createDirectories(src.getParent());
        Files.writeString(src, """
                package acme;

                /** Joins. */
                public class Join {

                    /**
                     * Joins two values.
                     *
                     * @param right the right value
                     * @param left the left value
                     */
                    public String join(String left, String right) {
                        return left + right;
                    }

                    /**
                     * Joins three, saying nothing about most of them.
                     *
                     * @param third the third
                     */
                    public String join(String first, String second, String third) {
                        return first + second + third;
                    }
                }
                """);
        Path jar = jarOf(dir, "join-1.0", src.toString());
        try (JarOutputStream out = new JarOutputStream(
                Files.newOutputStream(dir.resolve("join-1.0-sources.jar")))) {
            out.putNextEntry(new JarEntry("acme/Join.java"));
            out.write(Files.readAllBytes(src));
        }

        String api = api("acme.Join", jar);

        assertTrue(api.contains("join(String left, String right)"),
                "a tag names a parameter, it does not take a position:\n" + api);
        assertTrue(api.contains("join(String first, String second, String third)"),
                "and a parameter no tag mentions is still named as it was declared:\n" + api);
    }

    @Test
    void aNestedTypesConstructorIsFoundUnderTheNameItsSourceGivesIt() throws Exception {
        Path dir = Files.createTempDirectory("nested-ctor");
        Path src = dir.resolve("acme/Holder.java");
        Files.createDirectories(src.getParent());
        Files.writeString(src, """
                package acme;

                /** Holds. */
                public class Holder {

                    /** What is held. */
                    public static class Held {

                        /**
                         * Holds a thing.
                         *
                         * @param what the thing held
                         */
                        public Held(String what) {
                        }
                    }
                }
                """);
        Path jar = jarOf(dir, "holder-1.0", src.toString());
        try (JarOutputStream out = new JarOutputStream(
                Files.newOutputStream(dir.resolve("holder-1.0-sources.jar")))) {
            out.putNextEntry(new JarEntry("acme/Holder.java"));
            out.write(Files.readAllBytes(src));
        }

        String api = api("acme.Holder$Held", jar);

        assertTrue(api.contains("Holds a thing."), "the constructor's own doc is found:\n" + api);
        assertTrue(api.contains("Held(String what)"),
                "and it is named as its source declared it:\n" + api);
    }

    @Test
    void aNestedTypeTakesItsOwnAndNoneOfTheTypeItIsDeclaredIn() throws Exception {
        Path dir = Files.createTempDirectory("nested");
        Path src = dir.resolve("acme/Outer.java");
        Files.createDirectories(src.getParent());
        Files.writeString(src, """
                package acme;

                /** Documentation for Outer. */
                public class Outer {

                    /** Outer's own value. */
                    public String value(String a) {
                        return a;
                    }

                    /** Documentation for Inner. */
                    public static class Inner {
                        public String value(String a) {
                            return a;
                        }
                    }
                }
                """);
        Path jar = jarOf(dir, "outer-1.0", src.toString());
        try (JarOutputStream out = new JarOutputStream(
                Files.newOutputStream(dir.resolve("outer-1.0-sources.jar")))) {
            out.putNextEntry(new JarEntry("acme/Outer.java"));
            out.write(Files.readAllBytes(src));
        }

        String api = api("acme.Outer$Inner", jar);

        assertTrue(api.contains("Documentation for Inner."),
                "the nested type's own documentation is its own:\n" + api);
        assertTrue(!api.contains("Documentation for Outer."),
                "the enclosing type's own documentation is not this type's:\n" + api);
        assertTrue(!api.contains("Outer's own value."),
                "nor is a method of the enclosing type's documentation this method's:\n" + api);
        assertTrue(api.contains("value(String a)"),
                "and a method the nested type declares names its parameter as the nested type"
                        + " declared it, not as the enclosing type declared its own:\n" + api);
    }

    @Test
    void aJarWithNoSourcesBesideItGetsNoJavadocFromWhateverElseIsAround() throws Exception {
        Path dir = Files.createTempDirectory("wrong-version");
        Path oldSrc = dir.resolve("old/acme/Widget.java");
        Files.createDirectories(oldSrc.getParent());
        Files.writeString(oldSrc, """
                package acme;

                /** The old widget. */
                public final class Widget {
                    /**
                     * Spins it.
                     *
                     * @param turns how many turns
                     */
                    public void spin(int turns) {
                    }
                }
                """);
        Path oldJar = jarOf(dir, "widget-0.6.0", oldSrc.toString());

        // What the tool carries for the same name, from another version of the library.
        Path bundled = Files.createTempDirectory("bundled");
        Path carried = bundled.resolve("META-INF/souther-sources/acme/Widget.java");
        Files.createDirectories(carried.getParent());
        Files.writeString(carried, """
                package acme;

                /** The new widget, which is a different thing. */
                public final class Widget {
                    /**
                     * Rotates it about the axis.
                     *
                     * @param degrees how far around
                     */
                    public void spin(int degrees) {
                    }
                }
                """);

        ByteArrayOutputStream out = new ByteArrayOutputStream();
        try (java.net.URLClassLoader loader =
                     new java.net.URLClassLoader(new java.net.URL[]{bundled.toUri().toURL()}, null)) {
            assertEquals(0, JapiCommand.run(new String[]{"acme.Widget", "-cp", oldJar.toString()},
                    new PrintStream(out, true, StandardCharsets.UTF_8),
                    new PrintStream(OutputStream.nullOutputStream(), true, StandardCharsets.UTF_8), loader));
        }
        String api = out.toString(StandardCharsets.UTF_8);

        assertTrue(!api.contains("Rotates it about the axis.") && !api.contains("degrees"),
                "documentation for another copy of this name is not attached to the one on the class path:\n" + api);
        assertTrue(api.contains("spin(int arg0)"), api);
    }
}
