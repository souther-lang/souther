package souther.compiler;

import souther.compiler.stdlib.Stdlib;
import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How a module reaches the standard library (spec §stdlib): through the qualifier the name is
 * published under, or by importing the name and writing it bare. Nothing is delivered implicitly.
 *
 * <p>The rule is stated in the specification and enforced by the checker, and it has been described
 * in prose in several other places — a source comment, a Javadoc, a test name — which is how one of
 * them came to describe an older rule for weeks (issue #374). So it is fixed here as calls that
 * compile and calls that do not, and the report a bare name gets is derived from the published
 * surface rather than from a table someone maintains beside it.
 */
class AStandardLibraryNameIsReachedQualifiedOrImportedTest {

    /** The same module in two spellings, laid out line for line so only the call differs. */
    private static final String QUALIFIED = """
            module demo

            data In = { flag: Bool }
            data Out = { flag: Bool }

            behavior flip : (i: In) -> Out constructs Out

            let flip (i) = Out { flag = Bool.not(i.flag) }
            """;

    private static final String IMPORTED = """
            module demo
            import Bool ( not )
            data In = { flag: Bool }
            data Out = { flag: Bool }

            behavior flip : (i: In) -> Out constructs Out

            let flip (i) = Out { flag = not(i.flag) }
            """;

    @Test
    void aQualifiedNameNeedsNoImport() {
        Compiler.compile(QUALIFIED);
    }

    @Test
    void anImportedNameMayBeWrittenBare() {
        Compiler.compile(IMPORTED);
    }

    @Test
    void aBareNameWithNoImportIsRefusedAndBothRoutesAreOffered() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile(QUALIFIED.replace("Bool.not(", "not(")));

        String message = e.getMessage();
        assertTrue(message.contains("`Bool.not`"), message);
        assertTrue(message.contains("import"), "the import route is offered too: " + message);
    }

    /** A library value, which is written with no parameter list and applied to nothing. The rule is
     *  about names and not about calls, so a bare one is answered the same way. */
    private static final String VALUE = """
            module demo
            %s
            data In = { n: Int }
            data Out = { m: Map<String, Int> }

            behavior go : (i: In) -> Out constructs Out

            let go (i) = Out { m = %s }
            """;

    @Test
    void aLibraryValueIsReachedTheSameTwoWays() {
        Compiler.compile(VALUE.formatted("", "Map.empty"));
        Compiler.compile(VALUE.formatted("import Map ( empty )", "empty"));
    }

    @Test
    void aBareLibraryValueIsAnsweredLikeABareLibraryFunction() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile(VALUE.formatted("", "empty")));

        String message = e.getMessage();
        assertTrue(message.contains("`Map.empty`"), message);
        assertTrue(message.contains("`Set.empty`"), message);
        assertTrue(message.contains("import"), message);
        assertFalse(message.contains("I cannot find a value"), "not an unknown name: " + message);
    }

    @Test
    void aBareLibraryNameHandedOverAsAValueIsAnsweredToo() {
        // `not` is applied to nothing here — it is handed to a combinator. A nearby binding is the
        // wrong answer for it: the name exists, and how to reach it is known.
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { xs: List<Bool> }
                data Out = { ok: Bool }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = Out { ok = List.all(not, i.xs) }
                """));

        String message = e.getMessage();
        assertTrue(message.contains("`Bool.not`"), message);
        assertFalse(message.contains("did you mean"), "no nearby-name guess: " + message);
    }

    @Test
    void aModulesOwnNameStandsBesideTheLibrarysWithoutShadowingIt() {
        // Two spellings, two declarations: the bare one is this module's, the qualified one the
        // library's. Neither hides the other, so both may be called in one body.
        Compiler.compile("""
                module demo

                data In = { flag: Bool }
                data Out = { flag: Bool }

                behavior flip : (i: In) -> Out constructs Out

                let not (b: Bool) = b
                let flip (i) = Out { flag = not(Bool.not(i.flag)) }
                """);
    }

    @Test
    void importingANameBesideADeclarationOfItIsAConflictAndNotAShadowing() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                import Bool ( not )

                data In = { flag: Bool }
                data Out = { flag: Bool }

                behavior flip : (i: In) -> Out constructs Out

                let not (b: Bool) = b
                let flip (i) = Out { flag = not(i.flag) }
                """));

        assertTrue(e.getMessage().contains("conflicts with a definition of the same name"),
                e.getMessage());
    }

    @Test
    void whichSpellingWasWrittenIsSettledBeforeAnythingIsGenerated() {
        // Resolution answers what a bare name means, with the imports consulted last; every pass
        // after it reads the answer. So the two spellings of one call generate the same code —
        // except `$Module`, which records the imports as they were written for a reader of the jar.
        Map<String, byte[]> qualified = Compiler.compile(QUALIFIED);
        Map<String, byte[]> imported = Compiler.compile(IMPORTED);

        assertEquals(qualified.keySet(), imported.keySet());
        List<String> differing = qualified.keySet().stream()
                .filter(name -> !java.util.Arrays.equals(qualified.get(name), imported.get(name)))
                .toList();
        assertEquals(List.of(Emitted.declarations("demo")), differing,
                "only the class that records what was written differs");
    }

    @Test
    void theReportForABareNameOffersEveryModuleThatPublishesIt() {
        // The four a hand-written table had gone stale on: each is published by two modules, and a
        // report that named one of them was telling the reader the other did not exist.
        assertEquals(List.of("Map.insert", "Set.insert"), souther.compiler.DefaultStdlib.get().qualifiedCandidates("insert"));
        assertEquals(List.of("Map.remove", "Set.remove"), souther.compiler.DefaultStdlib.get().qualifiedCandidates("remove"));
        assertEquals(List.of("String.append", "List.append"), souther.compiler.DefaultStdlib.get().qualifiedCandidates("append"));
        assertEquals(List.of("Date.addDays", "DateTime.addDays"),
                souther.compiler.DefaultStdlib.get().qualifiedCandidates("addDays"));

        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { xs: Set<Int> }
                data Out = { xs: Set<Int> }

                behavior add : (i: In) -> Out constructs Out

                let add (i) = Out { xs = insert(1, i.xs) }
                """));
        assertTrue(e.getMessage().contains("`Map.insert`"), e.getMessage());
        assertTrue(e.getMessage().contains("`Set.insert`"), e.getMessage());
    }

    @Test
    void aPrivateHelperIsNotOfferedAsACandidate() {
        assertEquals(List.of(), souther.compiler.DefaultStdlib.get().qualifiedCandidates("foldFrom"));
    }

    @Test
    void everyCandidateListIsThePublishedSurfaceGroupedByBareName() {
        // Read from the bundled sources rather than from the tables the compiler built from them,
        // so this says the same thing twice from two directions instead of once from one.
        Map<String, List<String>> fromSource = declaredInTheBundledSources();

        for (Map.Entry<String, List<String>> e : fromSource.entrySet()) {
            assertEquals(e.getValue(), souther.compiler.DefaultStdlib.get().qualifiedCandidates(e.getKey()),
                    "the candidates for a bare `" + e.getKey() + "`");
        }
        // And nothing is offered that no module publishes: a name absent from the sources has no
        // candidates at all.
        assertEquals(List.of(), souther.compiler.DefaultStdlib.get().qualifiedCandidates("thereIsNoSuchFunction"));
        assertFalse(fromSource.isEmpty(), "the sources were read");
    }

    @Test
    void everyBundledSourceIsAModuleTheLanguageNames() {
        // The witness above reads the modules Reserved names. This is what keeps that from being
        // one table checked against itself: a `.sou` shipped in the reserved namespace and left out
        // of `Reserved.MODULES` would be a module nothing loads.
        Set<String> named = new LinkedHashSet<>();
        for (Reserved.StdlibModule module : Reserved.MODULES) {
            named.add(module.moduleName().substring(module.moduleName().indexOf('.') + 1) + ".sou");
        }

        assertEquals(named, bundledSourceFileNames());
        // Counted as well as compared, because a module listed twice would name a file that is
        // there and collapse into the set beside itself. `Reserved` refuses that where it is
        // written; this says the two are the same length, which is what the sets cannot.
        assertEquals(Reserved.MODULES.size(), bundledSourceFileNames().size(),
                "one entry per bundled source");
    }

    /** Every published name, by its bare name, in {@link Reserved#MODULES} order — read out of the
     *  bundled {@code .sou} text. */
    private static Map<String, List<String>> declaredInTheBundledSources() {
        // A top-level declaration starts at column 0; the `let`s inside a body are indented.
        Pattern declaration = Pattern.compile("(?m)^(private +)?let +([A-Za-z][A-Za-z0-9_]*) *[(:]");
        Map<String, List<String>> byBareName = new LinkedHashMap<>();
        for (Reserved.StdlibModule module : Reserved.MODULES) {
            String source = read("/" + module.moduleName().replace('.', '/') + ".sou");
            Matcher m = declaration.matcher(source);
            while (m.find()) {
                if (m.group(1) != null) {
                    continue;   // a helper the library keeps to itself; no caller may write it
                }
                byBareName.computeIfAbsent(m.group(2), bare -> new ArrayList<>())
                        .add(module.qualifier() + "." + m.group(2));
            }
        }
        // The sugar is declared in the compiler rather than in a source, so it is named here. A
        // sugar added without a line here fails this test, which is the point: it is part of the
        // surface a caller writes against.
        assertEquals(Set.of("List.fold"), souther.compiler.DefaultStdlib.get().rewrites().keySet(),
                "the sugared names this test knows about");
        byBareName.computeIfAbsent("fold", bare -> new ArrayList<>()).add("List.fold");
        byBareName.get("fold").sort((a, b) -> moduleOrder(a) - moduleOrder(b));
        return byBareName;
    }

    private static int moduleOrder(String qualifiedName) {
        String qualifier = qualifiedName.substring(0, qualifiedName.indexOf('.'));
        for (int i = 0; i < Reserved.MODULES.size(); i++) {
            if (Reserved.MODULES.get(i).qualifier().equals(qualifier)) {
                return i;
            }
        }
        throw new IllegalStateException("no standard-library module is written `" + qualifier + "`");
    }

    private static Set<String> bundledSourceFileNames() {
        // Anchored to a source the compiler itself loads, so the directory listed is the one it
        // reads from — `/souther/` alone would find the test tree's package of that name first.
        URL anchor = souther.compiler.check.StdlibLoader.class.getResource("/souther/bool.sou");
        if (anchor == null || !"file".equals(anchor.getProtocol())) {
            throw new IllegalStateException("the bundled sources are not readable as files");
        }
        try (Stream<Path> files = Files.list(Path.of(anchor.toURI()).getParent())) {
            return files.map(path -> path.getFileName().toString())
                    .filter(name -> name.endsWith(".sou"))
                    .collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new));
        } catch (IOException | java.net.URISyntaxException e) {
            throw new IllegalStateException(e);
        }
    }

    private static String read(String resource) {
        try (InputStream in = souther.compiler.check.StdlibLoader.class.getResourceAsStream(resource)) {
            if (in == null) {
                throw new IllegalStateException("missing bundled prelude resource " + resource);
            }
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
