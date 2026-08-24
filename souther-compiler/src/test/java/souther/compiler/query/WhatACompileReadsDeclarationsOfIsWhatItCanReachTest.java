package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;
import souther.compiler.meta.Agreement;
import souther.compiler.meta.DeclarationAgreement;
import souther.compiler.meta.PublishedClasses;
import souther.compiler.meta.ModuleReadback;
import souther.compiler.meta.Readback;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * The declarations a run holds an answer's own against are every module it can reach, not only the
 * ones this compilation built.
 *
 * <p>A model's own module is compiled here; a module it imports may have arrived compiled, and is
 * read off the path. Both are declarations a value crossing into an answer is read by, and a reader
 * that had only the first would find nothing for the second — on the side that is not in question.
 * What would then be reported is that the answer's classes cannot be read, of two builds that agree
 * about everything and one imported module neither of them has anything to do with.
 */
class WhatACompileReadsDeclarationsOfIsWhatItCanReachTest {

    private static final String SHARED = """
            module example.shared exposing ( Title )

            data Title = String
                invariant String.length(value) > 0
            """;

    private static final String ROOT = """
            module example.root
            import example.shared ( Title )

            data Todo = { title: Title, done: Bool }

            behavior rename : (t: Todo, to: Title) -> Todo
                constructs Todo

            let rename (t, to) = Todo { title = to, done = t.done }
            """;

    /** A module this compilation built, and one it read off the path, are both among them. */
    @Test
    void aModuleOnThePathIsAmongWhatThisCompileReadsDeclarationsOf() {
        PublishedClasses reads = declarationsOf(ROOT, Compiler.compile(SHARED));

        assertInstanceOf(Readback.Ready.class, ModuleReadback.read("example.root", reads, souther.compiler.DefaultStdlib.get().names()),
                "the module being compiled here");
        assertInstanceOf(Readback.Ready.class, ModuleReadback.read("example.shared", reads, souther.compiler.DefaultStdlib.get().names()),
                "and the one it imports, which arrived compiled");
    }

    /**
     * Two builds importing one compiled module agree.
     *
     * <p>The end of it: holding a run's declarations against an answer's walks the imports, and the
     * ordinary shape of a project has one of them arriving from a jar.
     */
    @Test
    void twoBuildsImportingOneCompiledModuleAgree() {
        Map<String, byte[]> onThePath = Compiler.compile(SHARED);

        Agreement held = DeclarationAgreement.of("example.root", "rename",
                declarationsOf(ROOT, onThePath), declarationsOf(ROOT, onThePath), souther.compiler.DefaultStdlib.get());

        assertInstanceOf(Agreement.Agree.class, held,
                "nothing a crossing depends on differs, and the imported module is read on both sides");
    }

    /** What a compile of {@code source} against {@code path} can read declarations of. */
    private static PublishedClasses declarationsOf(String source, Map<String, byte[]> path) {
        Compilation compiled = Compilation.ofSources(List.of(source), path::get);
        compiled.db().ask(new Output.All());
        org.junit.jupiter.api.Assertions.assertEquals(List.of(),
                compiled.diagnostics().values().stream().flatMap(List::stream)
                        .map(d -> String.valueOf(d.diagnostic().code())).toList(),
                "the model this is measured against compiles");
        return Output.declarationsRead(compiled.db());
    }
}
