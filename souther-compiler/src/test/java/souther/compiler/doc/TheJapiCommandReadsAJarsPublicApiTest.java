package souther.compiler.doc;

import org.junit.jupiter.api.BeforeAll;
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
 * `souther japi` answers a dependency's public API from its class files — what javap is reached
 * for today — and brings the javadoc along from the `-sources.jar` sitting next to the jar, which
 * javap never shows.
 */
class TheJapiCommandReadsAJarsPublicApiTest {

    private static Path jar;
    private static Path sourceOfGreeter;

    @BeforeAll
    static void aJarAndItsSourcesJar() throws Exception {
        Path dir = Files.createTempDirectory("japi-fixture");
        Path src = dir.resolve("acme/Greeter.java");
        sourceOfGreeter = src;
        Files.createDirectories(src.getParent());
        Files.writeString(src, """
                package acme;

                import java.util.List;

                /** Greets whoever is put in front of it. */
                public final class Greeter<T> {

                    /** What is said when nobody chose a greeting. */
                    @SuppressWarnings({"unchecked", "rawtypes"})
                    public static final Greeter<String> DEFAULT = new Greeter("hello");

                    public static final String DEFAULT_GREETING = "hello";

                    private String secret;

                    /** Says the greeting once per audience member. */
                    public <A> List<A> greet(A audience, int times) {
                        return List.of(audience);
                    }

                    Greeter(String secret) {
                        this.secret = secret;
                    }
                }
                """);
        Path hidden = dir.resolve("acme/Hidden.java");
        Files.writeString(hidden, """
                package acme;

                /** Not for anyone outside this package. */
                final class Hidden {
                    public String secret() {
                        return "s";
                    }
                }
                """);
        Path packageInfo = dir.resolve("acme/package-info.java");
        Files.writeString(packageInfo, """
                /** The acme package. */
                package acme;
                """);
        Path record = dir.resolve("acme/Pair.java");
        Files.writeString(record, """
                package acme;

                /** Two of anything, in order. */
                public record Pair<A, B>(A first, B second) {
                }
                """);
        JavaCompiler javac = ToolProvider.getSystemJavaCompiler();
        Path classes = dir.resolve("classes");
        Files.createDirectories(classes);
        assertEquals(0, javac.run(null, OutputStream.nullOutputStream(), OutputStream.nullOutputStream(),
                "-d", classes.toString(), "-parameters", src.toString(), record.toString(),
                hidden.toString(), packageInfo.toString()));

        jar = dir.resolve("greeter-1.0.jar");
        try (JarOutputStream out = new JarOutputStream(Files.newOutputStream(jar))) {
            try (Stream<Path> files = Files.walk(classes)) {
                for (Path f : files.filter(Files::isRegularFile).toList()) {
                    out.putNextEntry(new JarEntry(classes.relativize(f).toString()));
                    out.write(Files.readAllBytes(f));
                }
            }
        }
        try (JarOutputStream out = new JarOutputStream(
                Files.newOutputStream(dir.resolve("greeter-1.0-sources.jar")))) {
            out.putNextEntry(new JarEntry("acme/Greeter.java"));
            out.write(Files.readAllBytes(src));
            out.putNextEntry(new JarEntry("acme/Pair.java"));
            out.write(Files.readAllBytes(record));
        }
    }

    private record Answer(int code, String out, String err) {}

    private Answer run(String... args) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        int code = JapiCommand.run(args,
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(err, true, StandardCharsets.UTF_8));
        return new Answer(code, out.toString(StandardCharsets.UTF_8), err.toString(StandardCharsets.UTF_8));
    }

    @Test
    void aClassIsPrintedAsItsPublicMembersWithTheirGenerics() {
        Answer answer = run("acme.Greeter", "-cp", jar.toString());

        assertEquals(0, answer.code(), answer.err());
        assertTrue(answer.out().contains("public final class acme.Greeter<T>"), answer.out());
        assertTrue(answer.out().contains("public <A> java.util.List<A> greet(A audience, int times)"), answer.out());
        assertTrue(answer.out().contains("DEFAULT_GREETING"), answer.out());
    }

    @Test
    void whatIsNotPublicIsNotPartOfTheAnswer() {
        Answer answer = run("acme.Greeter", "-cp", jar.toString());

        assertTrue(answer.out().lines().noneMatch(l -> l.contains("secret")),
                "a private field stays out of the surface:\n" + answer.out());
        assertTrue(answer.out().lines().noneMatch(l -> l.contains("Greeter(String")),
                "a package-private constructor stays out too:\n" + answer.out());
    }

    @Test
    void javadocRidesAlongFromTheSourcesJarNextToTheJar() {
        Answer answer = run("acme.Greeter", "-cp", jar.toString());

        assertTrue(answer.out().contains("Greets whoever is put in front of it."), answer.out());
        assertTrue(answer.out().contains("Says the greeting once per audience member."), answer.out());
    }

    @Test
    void aRecordIsSaidAsARecordAndNotAsExtendingRecord() {
        Answer answer = run("acme.Pair", "-cp", jar.toString());

        assertEquals(0, answer.code(), answer.err());
        assertTrue(answer.out().contains("public record acme.Pair<A, B>"), answer.out());
        assertTrue(answer.out().lines().noneMatch(l -> l.contains("extends Record")), answer.out());
    }

    @Test
    void aDocumentedConstantKeepsItsDocEvenWhenItsInitializerCallsAConstructor() {
        Answer answer = run("acme.Greeter", "-cp", jar.toString());

        var lines = answer.out().lines().toList();
        int doc = lines.indexOf(lines.stream()
                .filter(l -> l.contains("What is said when nobody chose a greeting."))
                .findFirst().orElseThrow());
        assertTrue(lines.get(doc + 1).contains("DEFAULT"),
                "the doc sits on the field, not on a constructor its initializer mentions:\n" + answer.out());
    }

    @Test
    void javadocIsFoundInSourcesCarriedInsideTheJarItself() throws Exception {
        // The CLI is one shaded jar with its dependencies inside it and no `-sources.jar` beside
        // it, so this — not the sibling jar — is the path the ordinary invocation takes. The
        // sources have to be inside the very jar the class came from: a copy carried anywhere else
        // may describe another version of the same name.
        Path carrying = Files.createTempDirectory("carried").resolve("greeter-shaded.jar");
        try (java.util.jar.JarOutputStream out =
                     new java.util.jar.JarOutputStream(Files.newOutputStream(carrying));
             java.util.jar.JarFile source = new java.util.jar.JarFile(jar.toFile())) {
            for (java.util.jar.JarEntry e : source.stream().toList()) {
                out.putNextEntry(new JarEntry(e.getName()));
                out.write(source.getInputStream(e).readAllBytes());
            }
            out.putNextEntry(new JarEntry("META-INF/souther-sources/acme/Greeter.java"));
            out.write(Files.readAllBytes(sourceOfGreeter));
        }

        Answer answer = run("acme.Greeter", "-cp", carrying.toString());

        assertEquals(0, answer.code(), answer.err());
        assertTrue(answer.out().contains("Greets whoever is put in front of it."),
                "javadoc comes from the sources the jar carries: " + answer.out());
    }

    @Test
    void aSingleMemberIsAskedForByName() {
        Answer answer = run("acme.Greeter#greet", "-cp", jar.toString());

        assertEquals(0, answer.code(), answer.err());
        assertTrue(answer.out().contains("greet(A audience, int times)"), answer.out());
        assertTrue(answer.out().lines().noneMatch(l -> l.contains("DEFAULT_GREETING")),
                "only the member asked for is printed:\n" + answer.out());
    }

    @Test
    void aMemberThatIsNotThereNamesTheOnesThatAre() {
        Answer answer = run("acme.Greeter#salute", "-cp", jar.toString());

        assertEquals(2, answer.code());
        assertTrue(answer.err().contains("greet"), "the members it does have are offered: " + answer.err());
    }

    @Test
    void aPackageNameListsTheClassesUnderIt() {
        Answer answer = run("acme", "-cp", jar.toString());

        assertEquals(0, answer.code(), answer.err());
        assertTrue(answer.out().lines().anyMatch(l -> l.equals("acme.Greeter")), answer.out());
    }

    @Test
    void aClassPathEntryThatIsNotAnArchiveIsSaidAsSuchAndTheRestIsStillSearched() throws Exception {
        Path notAJar = Files.createTempFile("not-a", ".jar");
        Files.writeString(notAJar, "this is not a zip archive");

        Answer answer = run("acme.Greeter", "-cp", notAJar + java.io.File.pathSeparator + jar);

        assertEquals(0, answer.code(), "the readable jar beside it still answers: " + answer.err());
        assertTrue(answer.out().contains("class acme.Greeter"), answer.out());
        assertTrue(answer.err().contains(notAJar.getFileName().toString()),
                "the entry it could not read is named: " + answer.err());
    }

    @Test
    void aPackageListsOnlyWhatIsPublishedFromIt() {
        Answer answer = run("acme", "-cp", jar.toString());

        assertEquals(0, answer.code(), answer.err());
        assertTrue(answer.out().lines().anyMatch(l -> l.equals("acme.Greeter")), answer.out());
        assertTrue(answer.out().lines().noneMatch(l -> l.endsWith(".package-info")),
                "a package descriptor is not a type anyone calls:\n" + answer.out());
        assertTrue(answer.out().lines().noneMatch(l -> l.equals("acme.Hidden")),
                "a package-private type is not part of the published API:\n" + answer.out());
    }

    @Test
    void aTypeAskedForByNameIsShownEvenWhenItIsNotPublished() {
        Answer answer = run("acme.Hidden", "-cp", jar.toString());

        assertEquals(0, answer.code(), answer.err());
        assertTrue(answer.out().contains("class acme.Hidden"), answer.out());
        assertTrue(answer.err().contains("not public"),
                "and it is said that this is not part of the published API: " + answer.err());
    }

    @Test
    void aNameFoundNowhereSaysWhereItLooked() {
        Answer answer = run("acme.Nobody", "-cp", jar.toString());

        assertEquals(2, answer.code());
        assertTrue(answer.err().contains("acme.Nobody"), answer.err());
        assertTrue(answer.err().contains("greeter-1.0.jar"), "the classpath it searched is named: " + answer.err());
    }
}
