package souther.compiler.examples;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.RowIdentity;

import javax.tools.ToolProvider;

import java.io.File;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The face reads a model as a model is written, not as one file that imports nothing.
 *
 * <p>A module may write its rows beside itself and in an {@code examples for} file, and may import
 * another user module. A face taking one source and no dependency path would be narrower than the
 * language it stands in front of: a project using either would find its rows unreachable rather than
 * failing, which is worse than not offering the entrance at all.
 */
class TheFaceReadsWhatAModelIsWrittenAsTest {

    private static final String SHARED = """
            module example.ids exposing ( TodoId )

            data TodoId = Int
            """;

    private static final String MODEL = """
            module example.app

            import example.ids ( TodoId )

            data Title = String
            data Todo = { id: TodoId, title: Title, done: Bool }
            data NotFound = { id: TodoId }

            behavior findTodo : (id: TodoId) -> Todo | NotFound
            """;

    /** The rows, written where the language says they may be written and not beside the module. */
    private static final String COMPANION = """
            examples for example.app

            example findTodo
                | "a todo that is stored" : (TodoId(1))
                    -> Todo { id = TodoId(1), title = Title("write the SQL"), done = false }
                | (TodoId(99)) -> NotFound { id = TodoId(99) }
            """;

    private static final String IMPL = """
            package example.app;
            import example.ids.TodoId;
            public final class FindTodoImpl extends FindTodo {
                public FindTodoResult apply(TodoId id) {
                    // Another module's newtype arrives and is passed on: its constructor is not
                    // this package's to call, which is the position a real implementation is in.
                    return id.value() == 1L
                            ? new Todo(id, new Title("write the SQL"), false)
                            : new NotFound(id);
                }
            }
            """;

    /**
     * A module importing another user module, with its rows in an {@code examples for} file.
     *
     * <p>Both at once, because both were unreachable for one reason: the face read one source and
     * gave the compile an empty path.
     */
    @Test
    void aModuleThatImportsAnotherAndKeepsItsRowsBesideItRuns() throws Exception {
        BoundExamples examples = bound();

        List<RecordedRow> rows = examples.rows();
        assertEquals(2, rows.size(), "the companion file's rows are the module's rows");
        for (RecordedRow row : rows) {
            assertEquals(Disposition.HELD, examples.evaluate(row).disposition(), row.shown());
        }
    }

    /** Which module the rows are of is the binding's answer, not the order the files came in. */
    @Test
    void whichModuleIsBoundComesFromTheImplementation() throws Exception {
        SoutherExamples model = SoutherExamples.ofSources(List.of(SHARED, MODEL, COMPANION),
                ModulePath.EMPTY);

        assertTrue(model.modules().containsAll(List.of("example.ids", "example.app")),
                model.modules().toString());
        assertEquals(List.of("findTodo"), model.bind(implementation()).boundBehaviors());
    }

    /** A source that does not compile is refused with what the compiler says about it. */
    @Test
    void aModelThatDoesNotCompileIsRefusedWithItsDiagnostics() {
        CompileException refused = assertThrows(CompileException.class,
                () -> SoutherExamples.ofSource("""
                        module example.broken

                        data Todo = { id: NoSuchType }
                        """));

        assertFalse(refused.diagnostics().isEmpty(), "the diagnostics are kept, not their codes");
        assertEquals(refused.diagnostics().size(), refused.locatedDiagnostics().size(),
                "and each is still located in the source it is about");
        assertTrue(refused.pos().line() > 0, "with the position the compiler found it at");
    }

    /**
     * A key is made where it is resolved, and nowhere else.
     *
     * <p>The type closes it: there is no public constructor, so a name nothing answers to cannot be
     * written past the resolution and left to match no row. That is the setup that silently never
     * runs, which is what this type exists to prevent.
     */
    @Test
    void aKeyCannotBeWrittenForARowNothingAnswersTo() throws Exception {
        BoundExamples examples = bound();

        assertThrows(IllegalArgumentException.class,
                () -> examples.row("findTodo", "a todo that was never written"));
        assertEquals(0, RowKey.class.getConstructors().length,
                "nothing outside the package makes one");

        RowKey stored = examples.row("findTodo", "a todo that is stored");
        assertTrue(stored.is(examples.rows().get(0)));
        assertFalse(stored.is(examples.rows().get(1)));
    }

    /** A key of one enumeration is refused by another rather than quietly matching nothing. */
    @Test
    void aKeyOfOneBindingIsRefusedByAnothersRows() throws Exception {
        RowKey stored = bound().row("findTodo", "a todo that is stored");
        RecordedRow elsewhere = bound().rows().get(0);

        assertThrows(IllegalArgumentException.class, () -> stored.is(elsewhere));
    }

    /** An unnamed row is enumerated and has no address, which is the pair `RowKey` was split for. */
    @Test
    void anUnnamedRowIsRunnableAndUnaddressable() throws Exception {
        BoundExamples examples = bound();

        RecordedRow unnamed = examples.rows().get(1);
        assertEquals(new RowIdentity.Unnamed(2), unnamed.identity());
        assertEquals(Disposition.HELD, examples.evaluate(unnamed).disposition());
    }

    private static BoundExamples bound() throws Exception {
        return SoutherExamples.ofSources(List.of(SHARED, MODEL, COMPANION), ModulePath.EMPTY)
                .bind(implementation());
    }

    private static Object implementation() throws Exception {
        Path classes = Files.createTempDirectory("souther-sources");
        for (var e : souther.compiler.Compiler.compileModules(List.of(SHARED, MODEL)).entrySet()) {
            Path at = classes.resolve(e.getKey().replace('.', '/') + ".class");
            Files.createDirectories(at.getParent());
            Files.write(at, e.getValue());
        }
        Path java = classes.resolve("example/app/FindTodoImpl.java");
        Files.writeString(java, IMPL);
        java.io.ByteArrayOutputStream err = new java.io.ByteArrayOutputStream();
        int rc = ToolProvider.getSystemJavaCompiler().run(null, null, err,
                "-encoding", "UTF-8",
                "-classpath", classes + File.pathSeparator + System.getProperty("java.class.path"),
                "-d", classes.toString(), java.toString());
        assertEquals(0, rc, "the implementation compiles: " + err);
        URLClassLoader loader = new URLClassLoader(new URL[] {classes.toUri().toURL()},
                SoutherExamples.class.getClassLoader());
        return loader.loadClass("example.app.FindTodoImpl").getConstructor().newInstance();
    }
}
