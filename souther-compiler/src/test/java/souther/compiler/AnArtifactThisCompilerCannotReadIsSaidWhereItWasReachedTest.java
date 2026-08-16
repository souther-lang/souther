package souther.compiler;

import souther.compiler.codegen.Backend;
import souther.compiler.diag.Located;
import souther.compiler.meta.ModulePath;
import souther.compiler.meta.ModuleReadback;
import souther.compiler.meta.PublishedClasses;
import souther.compiler.meta.Readback;
import souther.compiler.query.Compilation;
import souther.compiler.source.SourceId;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A module the class path carries and this compiler will not read is one thing the author is told,
 * said at the {@code import} line that reaches it, and the rest of the compilation still answers.
 *
 * <p>Every way of failing used to be a raise, out of a walk over the whole path, from inside a text
 * this compiler assembled and nobody holds. What the author saw was a line and a column of a file
 * they do not have, for a module they did not write — and every other file's diagnostics went with
 * it, because a raise leaves the question that asked for the module rather than answering it.
 *
 * <p>The artifacts here are written by hand. A jar this compiler agrees with could not carry any of
 * these: the declaring project's own build would have refused the line. That is the case the
 * boundary revision exists for, and the case the compiler should be at its clearest.
 */
class AnArtifactThisCompilerCannotReadIsSaidWhereItWasReachedTest {

    /** A path whose declarations are written here rather than read off class files. */
    private record Fabricated(Map<String, PublishedClasses.Declarations> published)
            implements ModulePath {
        @Override
        public byte[] bytes(String binaryName) {
            return null;
        }

        @Override
        public PublishedClasses declarations() {
            return published::get;
        }
    }

    private static PublishedClasses.Declarations moduleClass(int compat, String module,
                                                             List<String> imports,
                                                             List<String> types,
                                                             List<String> helpers) {
        return new PublishedClasses.Declarations(new PublishedClasses.SoutherModuleView(
                compat, "0.0.1-other", module,
                "module " + module + " exposing ( " + String.join(", ", types) + " )",
                imports, types, List.of(), helpers), null, null, null);
    }

    private static PublishedClasses.Declarations dataClass(String declaration) {
        return new PublishedClasses.Declarations(null, declaration, null, null);
    }

    /** The importing project. Its second mistake is its own, and is how we see whether the rest of
     *  the file was still read. */
    private static final String APP = """
            module app.uses
            import lib.pub ( Held )

            data Page = { held: Held }
            data Bad = { x: NoSuchTypeAnywhere }
            """;

    private static Set<String> saidAboutTheSource(ModulePath path) {
        Compilation compilation = Compilation.ofSources(List.of(APP), path);
        Set<String> codes = new LinkedHashSet<>();
        for (Located said : compilation.diagnostics().get(new SourceId("0"))) {
            codes.add(said.diagnostic().code());
        }
        return codes;
    }

    /** Where the report about the artifact is said, in the file this compile does hold. */
    private static void bothAreSaidOnTheSource(ModulePath path) {
        Set<String> codes = saidAboutTheSource(path);
        assertTrue(codes.contains("E1509"), "the artifact is refused: " + codes);
        assertTrue(codes.contains("E1023"),
                "and the mistake in the author's own file is still said: " + codes);
    }

    /** The boundary revision does not agree. */
    @Test
    void oneBuiltByACompilerThatDisagrees() {
        bothAreSaidOnTheSource(new Fabricated(Map.of(
                "lib.pub.$Module", moduleClass(Backend.BOUNDARY_VERSION + 1, "lib.pub",
                        List.of(), List.of("Held"), List.of()),
                "lib.pub.Held", dataClass("data Held = String"))));
    }

    /** It names a declaration whose class the path does not carry. */
    @Test
    void oneWhoseDeclarationClassIsMissing() {
        bothAreSaidOnTheSource(new Fabricated(Map.of(
                "lib.pub.$Module", moduleClass(Backend.BOUNDARY_VERSION, "lib.pub",
                        List.of(), List.of("Held"), List.of()))));
    }

    /** What it published is not source this compiler parses. */
    @Test
    void oneWhosePublishedTextDoesNotParse() {
        bothAreSaidOnTheSource(new Fabricated(Map.of(
                "lib.pub.$Module", moduleClass(Backend.BOUNDARY_VERSION, "lib.pub",
                        List.of(), List.of("Held"), List.of()),
                "lib.pub.Held", dataClass("data Held = { ???"))));
    }

    /** Its import line names something this compiler's library does not publish. The helper is what
     *  makes the import needed, so it is not dropped before the check reads it. */
    @Test
    void oneWhoseImportLineCannotBeRead() {
        bothAreSaidOnTheSource(new Fabricated(Map.of(
                "lib.pub.$Module", moduleClass(Backend.BOUNDARY_VERSION, "lib.pub",
                        List.of("import List ( noSuchOperation )"), List.of("Held"),
                        List.of("let helper (xs) = noSuchOperation(xs)")),
                "lib.pub.Held", dataClass("data Held = String"))));
    }

    /**
     * The name a module took and what its artifact carries are two questions, and an artifact can be
     * wrong about both.
     *
     * <p>Asked in sequence, whichever failed first decided what the author heard, and fixing that one
     * brought the other out. They have different things to do about them — rebuild the dependency,
     * and rename the module — so telling one at a time is telling half of it.
     */
    @Test
    void oneThatTookAReservedNameAndCannotBeReadEitherIsBothThings() {
        Set<String> codes = new LinkedHashSet<>();
        Compilation compilation = Compilation.ofSources(List.of("""
                module app.uses
                import souther.taken ( Held )

                data Page = { held: Held }
                """), new Fabricated(Map.of(
                        "souther.taken.$Module", moduleClass(Backend.BOUNDARY_VERSION + 1,
                                "souther.taken", List.of(), List.of("Held"), List.of()),
                        "souther.taken.Held", dataClass("data Held = String"))));
        for (Located said : compilation.diagnostics().get(new SourceId("0"))) {
            codes.add(said.diagnostic().code());
        }

        assertTrue(codes.contains("E1502"), "the name is not one a module may take: " + codes);
        assertTrue(codes.contains("E1509"), "and what it carries cannot be read: " + codes);
    }

    /**
     * The negative control, and the whole of what {@code Readback.Failure} being a closed type is
     * for: a failure this compiler does not know the shape of stays a fault.
     *
     * <p>Converted, a defect in the compiler would reach the author as a diagnostic about their
     * dependency — an artifact reported as unreadable on the strength of a bug in the code reading
     * it. Which is what a catch around the reading, wide enough to hold every way of failing, does.
     */
    @Test
    void aFaultInTheReadingIsNotAnArtifactThisCompilerCannotRead() {
        PublishedClasses broken = _ -> {
            throw new IllegalStateException("a defect in the reader");
        };

        assertThrows(IllegalStateException.class, () -> ModuleReadback.read("lib.pub", broken),
                "a fault is not a statement about the artifact");
    }

    /** Reading one that is fine still answers a module, with its import lines read. */
    @Test
    void oneThisCompilerCanReadComesBackReady() {
        Map<String, byte[]> built = Compiler.compile("""
                module lib.ok exposing ( Held )
                data Held = String
                """);
        Readback readback = ModuleReadback.read("lib.ok",
                ((ModulePath) built::get).declarations());

        assertEquals("lib.ok",
                assertInstanceOf(Readback.Ready.class, readback).module().module().name());
    }
}
