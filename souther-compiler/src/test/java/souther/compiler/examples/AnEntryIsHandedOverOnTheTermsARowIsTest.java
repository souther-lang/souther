package souther.compiler.examples;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Disposition;
import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.RowOutcome;

import javax.tools.ToolProvider;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A stand-in entry is handed to a bound implementation on the terms a row is, and by the same gate.
 *
 * <p>The two comparisons answer different questions — a row is an obligation adjudicated, an entry
 * is a statement related to an observation — but what stands between the values and the
 * implementation is one thing. Asked separately, one of them goes unasked: `observe` reached the
 * implementation while `evaluate` was keeping rows away from it, so the same binding meant two
 * things depending on which call you made.
 */
class AnEntryIsHandedOverOnTheTermsARowIsTest {

    /** What the rows are written for. */
    private static final String MODEL = """
            module example.moved

            data TodoId = Int
            data Title = String
            data Todo = { id: TodoId, title: Title, done: Bool }
            data NotFound = { id: TodoId }

            behavior findTodo : (id: TodoId) -> Todo | NotFound

            fake findTodo
                | (TodoId(1)) -> Todo { id = TodoId(1), title = Title("write the SQL"), done = false }
                | _           -> NotFound { id = TodoId(0) }

            example findTodo
                | "a todo that is stored" : (TodoId(1))
                    -> Todo { id = TodoId(1), title = Title("write the SQL"), done = false }
            """;

    /** The same module as a later build has it: `Title` refuses values the build the implementation
     *  was compiled against admits, so a value crossing between the two is read by two different
     *  declarations. */
    private static final String NARROWED = MODEL.replace("data Title = String\n", """
            data Title = String
                invariant length(value) > 3
            """).replace("module example.moved\n", """
            module example.moved
            import String ( length )
            """);

    private static final String ANSWERS = """
            package example.moved;
            public final class FindTodoImpl extends FindTodo {
                public FindTodoResult apply(TodoId id) {
                    return id.equals(new TodoId(1L))
                            ? new Todo(new TodoId(1L), new Title("write the SQL"), false)
                            : new NotFound(id);
                }
            }
            """;

    /** An implementation that also carries an unrelated `apply` of the same arity. */
    private static final String OVERLOADED = """
            package example.moved;
            public final class FindTodoImpl extends FindTodo {
                public FindTodoResult apply(TodoId id) {
                    return id.equals(new TodoId(1L))
                            ? new Todo(new TodoId(1L), new Title("write the SQL"), false)
                            : new NotFound(id);
                }

                public String apply(String debug) {
                    throw new AssertionError("the behavior's `apply` is not this one");
                }

                public String apply(Integer alsoNotIt) {
                    throw new AssertionError("nor this one");
                }
            }
            """;

    private static final String RAN_ON = "souther.test.the.implementation.ran.on";

    /** An implementation that writes down which thread applied it. */
    private static final String RECORDS_ITS_THREAD = """
            package example.moved;
            public final class FindTodoImpl extends FindTodo {
                public FindTodoResult apply(TodoId id) {
                    System.setProperty("%s", Thread.currentThread().getName());
                    return id.equals(new TodoId(1L))
                            ? new Todo(new TodoId(1L), new Title("write the SQL"), false)
                            : new NotFound(id);
                }
            }
            """.formatted(RAN_ON);

    /**
     * A binding a row may not be handed to is not handed an entry either.
     *
     * <p>The implementation was built against a build whose `Title` admits what this one refuses, so
     * its decoder reads a row's values by declarations that are not this module's. `evaluate` stops
     * at {@code ANSWERER_ESTABLISHMENT}; `observe` must not walk past the same finding and apply it.
     */
    @Test
    void anEntryIsNotObservedAgainstAnImplementationOfAnotherBuild() throws Exception {
        BoundExamples examples = SoutherExamples.ofSource(NARROWED)
                .bind(builtFrom(MODEL, ANSWERS));

        RowOutcome row = examples.evaluate(examples.rows().get(0)).outcome();
        assertEquals(Disposition.INCOMPLETE, row.disposition());
        assertEquals(FailurePhase.ANSWERER_ESTABLISHMENT, row.failurePhase(),
                "the row is kept away from it");

        StandinObservation observed = examples.observe(examples.standinEntries().get(0));
        StandinObservation.Unobserved unobserved = assertInstanceOf(
                StandinObservation.Unobserved.class, observed,
                "and so is the entry, rather than the two builds disagreeing being reported as the"
                        + " stand-in and the implementation disagreeing");
        assertInstanceOf(StandinObservation.Reason.TheImplementationIsOfAnotherBuild.class,
                unobserved.why());
    }

    /**
     * The control: declarations that agree hand both over.
     *
     * <p>The same source, compiled twice into two loaders. Same declarations and two type universes,
     * which is the crossing without the staleness — so what the test above measured is the
     * disagreement and not the crossing.
     */
    @Test
    void anEntryIsObservedWhereTheTwoBuildsAgree() throws Exception {
        BoundExamples examples = SoutherExamples.ofSource(MODEL)
                .bind(builtFrom(MODEL, ANSWERS));

        assertEquals(Disposition.HELD, examples.evaluate(examples.rows().get(0)).outcome().disposition());
        assertInstanceOf(StandinObservation.AsStated.class,
                examples.observe(examples.standinEntries().get(0)));
    }

    /**
     * A bound implementation runs on the thread that asked for it.
     *
     * <p>What it answers out of is the caller's world, and a thread is part of a world: a
     * transaction bound to one, a security or request context, an MDC, a scoped value. A run of this
     * compile's own code goes to a worker of its own, and moving a supplied implementation there too
     * would take it out of the world the caller arranged — with nothing in a synchronous
     * {@code evaluate(row)} to say so.
     *
     * <p>Both operations, because both observe a world the caller arranged between calls. One of
     * them running elsewhere would be the binding meaning two things again.
     *
     * <p>The row around it is not here: it runs on a worker of this compile's own and stays there,
     * and only the application crosses back. What holds that boundary is
     * {@code TheRowStaysOnItsWorkerAndTheApplicationDoesNotTest}; what this holds is the half a
     * caller sees.
     */
    @Test
    void aBoundImplementationRunsWhereItWasCalledFrom() throws Exception {
        BoundExamples examples = SoutherExamples.ofSource(MODEL)
                .bind(builtFrom(MODEL, RECORDS_ITS_THREAD));

        examples.evaluate(examples.rows().get(0));
        assertEquals(Thread.currentThread().getName(), System.getProperty(RAN_ON),
                "the row's evaluation applied it here");

        System.clearProperty(RAN_ON);
        examples.observe(examples.standinEntries().get(0));
        assertEquals(Thread.currentThread().getName(), System.getProperty(RAN_ON),
                "and so did the entry's observation");
    }

    /**
     * The behavior's `apply` is the one the base declares, whichever others the class carries.
     *
     * <p>Read off the instance by name and arity, an unrelated `apply(String)` is as good a
     * candidate as the behavior's, and which one ran would depend on the order
     * {@code Class#getMethods} happens to answer in.
     */
    @Test
    void theApplyThatRunsIsTheOneTheBaseDeclares() throws Exception {
        BoundExamples examples = SoutherExamples.ofSource(MODEL)
                .bind(builtFrom(MODEL, OVERLOADED));

        assertEquals(Disposition.HELD, examples.evaluate(examples.rows().get(0)).outcome().disposition(),
                "the behavior's own `apply` answered, and neither of the decoys");
        assertInstanceOf(StandinObservation.AsStated.class,
                examples.observe(examples.standinEntries().get(0)));
    }

    /** {@code source} compiled, then {@code impl} compiled against it, in a loader of its own. */
    private static Object builtFrom(String source, String impl) throws Exception {
        Path classes = Files.createTempDirectory("souther-terms");
        for (var e : souther.compiler.Compiler.compileModules(List.of(source)).entrySet()) {
            Path at = classes.resolve(e.getKey().replace('.', '/') + ".class");
            Files.createDirectories(at.getParent());
            Files.write(at, e.getValue());
        }
        Path java = classes.resolve("example/moved/FindTodoImpl.java");
        Files.writeString(java, impl);
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        int rc = ToolProvider.getSystemJavaCompiler().run(null, null, err,
                "-encoding", "UTF-8",
                "-classpath", classes + File.pathSeparator + System.getProperty("java.class.path"),
                "-d", classes.toString(), java.toString());
        assertEquals(0, rc, "the implementation compiles: " + err);
        URLClassLoader loader = new URLClassLoader(new URL[] {classes.toUri().toURL()},
                SoutherExamples.class.getClassLoader());
        return loader.loadClass("example.moved.FindTodoImpl").getConstructor().newInstance();
    }

    /** Kept so a reader sees the narrowed model is a model and not a broken one: what stops the row
     *  above is the two builds disagreeing, not a source that does not compile. */
    @Test
    void theNarrowedModuleCompilesOnItsOwn() {
        assertTrue(SoutherExamples.ofSource(NARROWED).modules().contains("example.moved"));
    }
}
