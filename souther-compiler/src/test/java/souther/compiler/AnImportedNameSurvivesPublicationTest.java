package souther.compiler;

import souther.compiler.check.Resolve;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Names;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A module may import the names it wants and then write them bare, and a module is published as the
 * source that declared it. So an invariant that calls a bare imported name has to mean the same
 * thing read back out of a jar as it does in the project that wrote it: what the import brought in
 * is part of what the declaration says, and travels with it.
 *
 * <p>Whether the module was compiled here or read off the class path does not enter into it — the
 * specification says as much of a construction's discharge, and it is the same reading.
 */
class AnImportedNameSurvivesPublicationTest {

    private static final String BARE = """
            module lib.text exposing ( Title )
            import String ( length )

            data Title = String
                invariant length(value) > 0
            """;

    private static final String QUALIFIED = """
            module lib.text exposing ( Title )

            data Title = String
                invariant String.length(value) > 0
            """;

    private static final String IMPORTING = """
            module app.uses
            import lib.text ( Title )

            data Note = { title: Title }
            """;

    private static ModulePath published(String source) {
        Map<String, ClassFileImage> classes = Compiler.compile(source);
        return ModulePath.of(classes);
    }

    @Test
    void anInvariantCallingABareImportedNameReadsBack() {
        assertTrue(Compiler.compileModules(List.of(IMPORTING), published(BARE))
                .containsKey("app.uses.Note"));
    }

    /** The helpers an invariant calls travel with it, and are read back under the same imports. */
    @Test
    void aPublishedHelperCallingABareImportedNameReadsBack() {
        ModulePath path = published("""
                module lib.text exposing ( Title )
                import String ( length )

                data Title = String
                    invariant nonEmpty(value)

                let nonEmpty (s: String) = length(s) > 0
                """);

        assertTrue(Compiler.compileModules(List.of(IMPORTING), path)
                .containsKey("app.uses.Note"));
    }

    /** The import line writes both halves of a library name, and the alias is the half a published
     *  module is read back under. */
    @Test
    void anAliasedLibraryImportReadsBack() {
        ModulePath path = published("""
                module lib.text exposing ( Title )
                import String as S ( length )

                data Title = String
                    invariant length(value) > 0
                """);

        assertTrue(Compiler.compileModules(List.of(IMPORTING), path)
                .containsKey("app.uses.Note"));
    }

    /** A module off the path brings its own reaches with it, and each of them is read back the same
     *  way — a dependency of a dependency is not read under weaker rules. */
    @Test
    void aModuleReachedThroughAnotherOnThePathReadsBack() {
        Map<String, ClassFileImage> base = Compiler.compile(BARE);
        Map<String, ClassFileImage> mid = Compiler.compileModules(List.of("""
                module lib.doc exposing ( Doc )
                import lib.text ( Title )

                data Doc = { title: Title }
                """), ModulePath.of(base));

        // The near module over the one it was built against, which is the order a path is read in.
        Map<String, ClassFileImage> reached = new java.util.LinkedHashMap<>(base);
        reached.putAll(mid);
        Map<String, ClassFileImage> app = Compiler.compileModules(List.of("""
                module app.uses
                import lib.doc ( Doc )

                data Page = { doc: Doc }
                """), ModulePath.of(reached));

        assertTrue(app.containsKey("app.uses.Page"));
    }

    /**
     * The two spellings are one declaration, so they are read back as one.
     *
     * <p>Measured on what the name denotes and not on the tree it was written as: the import line
     * lets a name be written without its qualifier and says nothing else, so the two differ in their
     * text and in nothing a reader of the declaration is answered.
     */
    @Test
    void theTwoSpellingsDenoteTheSameLibraryOperation() {
        assertEquals(Set.of(ValueName.Stdlib.operation("String", "length")), libraryNamesDenotedBy(BARE));
        assertEquals(libraryNamesDenotedBy(QUALIFIED), libraryNamesDenotedBy(BARE),
                "an import line changes how a name is written and not what it means");
    }

    /** What the invariant of {@code lib.text} denotes, read back off the classes {@code source}
     *  compiled to, in a project that has no source for it. */
    private static Set<ValueName.Stdlib> libraryNamesDenotedBy(String source) {
        Compilation compilation = Compilation.ofSources(List.of(IMPORTING), published(source));
        compilation.answerEverything();
        Resolve.ResolutionIndex facts =
                compilation.db().ask(new Names.Facts("lib.text")).value();
        Set<ValueName.Stdlib> denoted = new LinkedHashSet<>();
        for (Resolve.ValueUse use : facts.values()) {
            if (use.denotes() instanceof ValueName.Stdlib operation
                    && !operation.isNamespace()) {
                denoted.add(operation);
            }
        }
        return denoted;
    }

    /**
     * The failing route this was found on. A compile driven through the query API answered no
     * classes and no diagnostics at all: the report was about a module no source of the compile
     * declared, and was dropped for having nowhere to go.
     */
    @Test
    void theQueryApiEmitsTheSameClassesForEitherSpelling() {
        assertEquals(classesFor(QUALIFIED), classesFor(BARE));
        assertFalse(classesFor(BARE).isEmpty(), "nothing was emitted and nothing was said");
    }

    private static Set<String> classesFor(String source) {
        Compilation compilation = Compilation.ofSources(List.of(IMPORTING), published(source));
        compilation.answerEverything();
        return compilation.classes().keySet();
    }
}
