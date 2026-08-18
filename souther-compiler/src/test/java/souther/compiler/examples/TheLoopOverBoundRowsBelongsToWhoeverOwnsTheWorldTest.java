package souther.compiler.examples;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

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
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The face is an enumeration of rows and the evaluation of one, and the loop over them is not here.
 *
 * <p>The reason is not test-framework hygiene. A bound implementation answers out of world state,
 * that state is the caller's, and it changes between one row and the next — so the owner of what
 * changes between iterations owns the loop. The implementation here answers out of a system
 * property, which is a world as much as a table is: the same row is evaluated twice under two of
 * them and answers differently, which is two observations and not a contradiction.
 *
 * <p>A bulk {@code evaluate()} would own that loop, and the hooks it would then grow — before,
 * after, around, transaction, retry, parallelism — are a test framework, which exists.
 */
class TheLoopOverBoundRowsBelongsToWhoeverOwnsTheWorldTest {

    private static final String STORED = "souther.test.a.todo.is.stored";

    private static final String MODEL = """
            module example.stored

            data TodoId = Int
            data Title = String
            data Todo = { id: TodoId, title: Title, done: Bool }
            data NotFound = { id: TodoId }

            behavior findTodo : (id: TodoId) -> Todo | NotFound

            example findTodo
                | "a todo that is stored" : (TodoId(1))
                    -> Todo { id = TodoId(1), title = Title("write the SQL"), done = false }
                | (TodoId(99)) -> NotFound { id = TodoId(99) }
            """;

    /** Answers out of the world, which here is a property the caller sets between evaluations. */
    private static final String IMPL = """
            package example.stored;
            public final class FindTodoImpl extends FindTodo {
                public FindTodoResult apply(TodoId id) {
                    boolean stored = "yes".equals(System.getProperty("%s"));
                    return stored && id.equals(new TodoId(1L))
                            ? new Todo(new TodoId(1L), new Title("write the SQL"), false)
                            : new NotFound(id);
                }
            }
            """.formatted(STORED);

    @AfterEach
    void forgetTheWorld() {
        System.clearProperty(STORED);
    }

    /** Both rows, named as they were written, and the one written without a name still enumerated. */
    @Test
    void theRowsAreTheOnesTheBindingMakesRunnable() throws Exception {
        List<RecordedRow> rows = bound().rows();

        assertEquals(2, rows.size());
        assertEquals(List.of("findTodo", "findTodo"),
                rows.stream().map(RecordedRow::behavior).toList());
        assertInstanceOf(RowIdentity.Named.class, rows.get(0).identity());
        assertInstanceOf(RowIdentity.Unnamed.class, rows.get(1).identity(),
                "a row written without a name is enumerated, and cannot be addressed");
        assertEquals(List.of("a todo that is stored", "#2"),
                rows.stream().map(RecordedRow::shown).toList());
    }

    /**
     * One row, evaluated twice under two worlds.
     *
     * <p>The row is the same value both times and nothing of the first evaluation reaches the
     * second. What the two answers say is what the implementation answered in each world, which is
     * the intended use and not a contradiction to be reconciled here.
     */
    @Test
    void oneRowEvaluatedUnderTwoWorldsIsTwoObservations() throws Exception {
        BoundExamples examples = bound();
        RowKey key = examples.row("findTodo", "a todo that is stored");
        RecordedRow stored = examples.rows().stream().filter(key::is).findFirst().orElseThrow();

        System.setProperty(STORED, "yes");
        assertEquals(Disposition.HELD, examples.evaluate(stored).disposition(),
                "the row holds in the world it was written for");

        System.clearProperty(STORED);
        assertEquals(Disposition.FAILED, examples.evaluate(stored).disposition(),
                "and does not in the world where nothing is stored");
    }

    /** A row that has no name runs, which is why evaluation takes the row and not the key. */
    @Test
    void aRowWithNoNameStillRuns() throws Exception {
        BoundExamples examples = bound();
        RecordedRow unnamed = examples.rows().get(1);

        assertEquals(Disposition.HELD, examples.evaluate(unnamed).disposition(),
                "nothing is stored under 99 in any world this test arranges");
    }

    /** A name nothing answers to fails where it is resolved, not as setup that never runs. */
    @Test
    void anAddressIsResolvedAgainstTheRowsAsWritten() throws Exception {
        BoundExamples examples = bound();

        assertEquals("a todo that is stored", examples.row("findTodo", "a todo that is stored").name());
        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> examples.row("findTodo", "a todo that was never written"));
        assertTrue(refused.getMessage().contains("a todo that was never written"),
                refused.getMessage());
    }

    /** A handle belongs to the enumeration that made it. */
    @Test
    void aRowOfOneBindingIsRefusedByAnother() throws Exception {
        RecordedRow itsOwn = bound().rows().get(0);
        BoundExamples other = bound();

        assertThrows(IllegalArgumentException.class, () -> other.evaluate(itsOwn));
    }

    private static BoundExamples bound() throws Exception {
        return SoutherExamples.ofSource(MODEL).bind(builtElsewhere());
    }

    /** The implementation, compiled against the module's classes and loaded from its own loader. */
    private static Object builtElsewhere() throws Exception {
        Path classes = Files.createTempDirectory("souther-world");
        for (var e : souther.compiler.Compiler.compileModules(List.of(MODEL)).entrySet()) {
            Path at = classes.resolve(e.getKey().replace('.', '/') + ".class");
            Files.createDirectories(at.getParent());
            Files.write(at, e.getValue());
        }
        Path java = classes.resolve("example/stored/FindTodoImpl.java");
        Files.writeString(java, IMPL);
        int rc = ToolProvider.getSystemJavaCompiler().run(null, null, null,
                "-encoding", "UTF-8",
                "-classpath", classes + File.pathSeparator + System.getProperty("java.class.path"),
                "-d", classes.toString(), java.toString());
        assertEquals(0, rc, "the implementation compiles against the module's classes");
        URLClassLoader loader = new URLClassLoader(new URL[] {classes.toUri().toURL()},
                SoutherExamples.class.getClassLoader());
        return loader.loadClass("example.stored.FindTodoImpl").getConstructor().newInstance();
    }
}
