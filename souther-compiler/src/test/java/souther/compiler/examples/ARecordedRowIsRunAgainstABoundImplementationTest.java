package souther.compiler.examples;

import org.junit.jupiter.api.Test;

import souther.compiler.generated.EvaluationArtifact;
import souther.compiler.meta.ClassFileDeclarations;
import souther.compiler.meta.PublishedClasses;
import souther.compiler.observe.Applied;
import souther.compiler.observe.Counting;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.Stage;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;

import javax.tools.ToolProvider;

import java.io.File;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row recorded against an injected behavior, run against a Java implementation the evaluation was
 * given.
 *
 * <p>ADR-0088 made such a row a record of what the behavior owes: its arity is checked, its inputs
 * are built through their derived decoders and held to their invariants, its expectation is held to
 * the output's cases, and there it stops as {@code PENDING}. What is held here is the other half —
 * the row deciding whether the implementation answers what the model says it owes.
 *
 * <p>The implementation is compiled by {@code javac} against the module's classes written to a
 * directory, and loaded from that directory. That is the position a real one is in and not a
 * simulation of it: it extends a base of a build that is not this run's, its classes are its own
 * loader's, and nothing of this compile's may be handed to it. An implementation given this run's
 * own values fails on the first cast inside itself.
 */
class ARecordedRowIsRunAgainstABoundImplementationTest {

    private static final String MODEL = """
            module example.todo
            import String ( length )

            data TodoId = Int
            data Title = String
                invariant length(value) > 0

            data Todo = { id: TodoId, title: Title, done: Bool }
            data NotFound = { id: TodoId }

            behavior findTodo : (id: TodoId) -> Todo | NotFound

            example findTodo
                | "a todo that is stored" : (TodoId(1))
                    -> Todo { id = TodoId(1), title = Title("write the SQL"), done = false }
                | "an id nothing is stored under" : (TodoId(99))
                    -> NotFound { id = TodoId(99) }
            """;

    /** Answers both rows the way the model says it owes. */
    private static final String ANSWERS = """
            package example.todo;
            public final class FindTodoImpl extends FindTodo {
                public FindTodoResult apply(TodoId id) {
                    return id.equals(new TodoId(1L))
                            ? new Todo(new TodoId(1L), new Title("write the SQL"), false)
                            : new NotFound(id);
                }
            }
            """;

    /** Answers the stored id with the wrong title, which is what a query mapping two columns the
     *  wrong way round does. */
    private static final String MISMAPS = """
            package example.todo;
            public final class FindTodoImpl extends FindTodo {
                public FindTodoResult apply(TodoId id) {
                    return id.equals(new TodoId(1L))
                            ? new Todo(new TodoId(1L), new Title("read the SQL"), false)
                            : new NotFound(id);
                }
            }
            """;

    /**
     * The same model, with the behavior stating a relation between what it is given and what it
     * answers.
     *
     * <p>Nothing in the generated surface carries it: an injected behavior's base class is the same
     * class whether or not a clause is written, so the agent writing the SQL cannot see the contract
     * in what it extends.
     */
    private static final String DECLARING = MODEL.replace(
            "behavior findTodo : (id: TodoId) -> Todo | NotFound\n",
            """
            behavior findTodo : (id: TodoId) -> Todo | NotFound
                ensures Todo -> value.id.value == id.value
            """);

    /** Answers the stored row with a todo carrying an id nobody asked for. */
    private static final String ANSWERS_ABOUT_ANOTHER = """
            package example.todo;
            public final class FindTodoImpl extends FindTodo {
                public FindTodoResult apply(TodoId id) {
                    return id.equals(new TodoId(1L))
                            ? new Todo(new TodoId(7L), new Title("write the SQL"), false)
                            : new NotFound(id);
                }
            }
            """;

    /**
     * What the implementation answered, held to what the behavior declares.
     *
     * <p>This is the only place such an answer is ever checked when the application's own Java is
     * what calls the behavior: there is no body to check in, and a behavior nothing in the module
     * calls has no crossing into generated code either.
     *
     * <p>The row is stopped at {@code ENSURES} and before its own comparison — what the answer
     * disagrees with is the model, and a row told only that it expected one value and saw another
     * would send its author to look at the row.
     */
    @Test
    void whatAnInjectedImplementationAnsweredIsHeldToWhatTheBehaviorDeclares() throws Exception {
        ExampleVerifier.Observations observed = evaluated(DECLARING, ANSWERS_ABOUT_ANOTHER);

        RowOutcome stored = named(observed, "a todo that is stored");
        assertEquals(Disposition.FAILED, stored.disposition());
        assertEquals(FailurePhase.ENSURES, stored.failurePhase(),
                "and not COMPARISON, which is the row disagreeing rather than the model");
        assertTrue(reasons(observed).contains("E1930"), reasons(observed).toString());
    }

    /** The control: the same declaration, kept. */
    @Test
    void anImplementationThatKeepsTheDeclarationIsNotStoppedByIt() throws Exception {
        ExampleVerifier.Observations observed = evaluated(DECLARING, ANSWERS);

        assertEquals(List.of(), reasons(observed));
        for (RowOutcome row : observed.rows()) {
            assertEquals(Disposition.HELD, row.disposition(), row.identity().shown());
        }
    }

    /** The row it owes, held against what the implementation answered. */
    @Test
    void aPendingRowIsDecidedByTheImplementationTheEvaluationWasGiven() throws Exception {
        ExampleVerifier.Observations observed = evaluated(ANSWERS);

        assertEquals(List.of(), reasons(observed), "the implementation answers what it owes");
        assertEquals(2, observed.rows().size());
        for (RowOutcome row : observed.rows()) {
            assertEquals(Disposition.HELD, row.disposition(), row.identity().shown());
            assertEquals(Stage.COMPARED, row.stage());
            assertEquals(FailurePhase.NONE, row.failurePhase());
        }
    }

    /** What applied it is the third arm, and a reader telling the arms apart can. */
    @Test
    void theRowSaysABindingAppliedIt() throws Exception {
        for (RowOutcome row : evaluated(ANSWERS).rows()) {
            assertInstanceOf(Applied.Bound.class, row.run().applied());
        }
    }

    /**
     * A bound row's counting is read, and what it read is the fixtures'.
     *
     * <p>{@link Counting.Unread} is an evaluation given up on; answering it for a row nothing this
     * compile instrumented ran through would put back together the two axes #717 separated. The
     * steps are not zero and that is the same fact from the other side: {@code Title}'s invariant is
     * this compile's code and the row's fixture goes through it, so what is counted covers the
     * fixtures and stops at the behavior — which is injected, has no body, and has nothing to count.
     *
     * <p>{@code hits} is empty, so a measure reading it sees no arm this row failed to reach.
     */
    @Test
    void aBoundRowsCountingIsReadAndCoversItsFixturesOnly() throws Exception {
        for (RowOutcome row : evaluated(ANSWERS).rows()) {
            Counting.Read read = assertInstanceOf(Counting.Read.class, row.run().counting(),
                    "the counting was read");
            assertEquals(java.util.Set.of(), read.hits(),
                    "and lit no branch, there being no body to light one");
        }
    }

    /** The row that would catch the defect catches it, and the one that would not stays held. */
    @Test
    void anImplementationThatAnswersOtherwiseFailsTheRowThatSaysSo() throws Exception {
        ExampleVerifier.Observations observed = evaluated(MISMAPS);

        RowOutcome stored = named(observed, "a todo that is stored");
        RowOutcome missing = named(observed, "an id nothing is stored under");
        assertEquals(Disposition.FAILED, stored.disposition());
        assertEquals(FailurePhase.COMPARISON, stored.failurePhase());
        assertEquals(Disposition.HELD, missing.disposition(),
                "the row the defect does not reach is not evidence against it");
        assertTrue(reasons(observed).contains("E1905"),
                "and the row is told the way a row that disagrees is told: " + reasons(observed));
    }

    private static RowOutcome named(ExampleVerifier.Observations observed, String name) {
        return observed.rows().stream()
                .filter(r -> r.identity().shown().equals(name))
                .findFirst().orElseThrow(() -> new AssertionError("no row named `" + name + "`"));
    }

    private static List<String> reasons(ExampleVerifier.Observations observed) {
        return observed.failures().stream().map(f -> String.valueOf(f.code())).toList();
    }

    /** The module's rows, run against {@code implementation} as a build that is not this one's. */
    private static ExampleVerifier.Observations evaluated(String implementation) throws Exception {
        return evaluated(MODEL, implementation);
    }

    private static ExampleVerifier.Observations evaluated(String model, String implementation)
            throws Exception {
        Compilation c = Compilation.ofSource(model, "Main");
        c.db().ask(new Output.All());
        assertEquals(List.of(), c.diagnostics().values().stream().flatMap(List::stream)
                        .map(d -> String.valueOf(d.diagnostic().code())).toList(),
                "the model whose rows are run compiles");
        String name = c.modules().get(0);
        EvaluationArtifact artifact = c.db()
                .ask(new Output.EvaluationLinked(name, Output.CoverageMode.NONE)).value();
        assertEquals(List.of(), c.diagnostics().values().stream().flatMap(List::stream)
                        .map(d -> String.valueOf(d.diagnostic().code())).toList(),
                "the model whose rows are run compiles");

        Object bound = builtElsewhere(c.db().ask(new Output.All()).value(), implementation);
        ClassLoader parent = ExampleVerifier.class.getClassLoader();
        return ExampleVerifier.check(
                c.db().ask(new Shapes.Prepared(name)).value().forExamples(),
                Scopes.derived(c.db(), name).value(),
                c.db().ask(new Bodies.Signatures(name)).value(),
                artifact,
                declarationsOf(c),
                c.db().ask(new Bodies.Requirements(name)).value(),
                parent,
                c.db().ask(new Bodies.ModuleDefinitions(name)).value(),
                Deadline.ofMillis(EvaluationPolicy.DEFAULT.outerTimeout().toMillis()),
                EvaluationPolicy.DEFAULT,
                Answering.bound(bound, c.db().ask(new Bodies.Signatures(name)).value()),
                c.db().ask(new Bodies.Contracts(name)).value());
    }

    /** What the module's rows are written for, as this compile emitted it. */
    private static java.util.function.Supplier<PublishedClasses> declarationsOf(Compilation c) {
        Map<String, byte[]> classes = c.db().ask(new Output.All()).value();
        return () -> new ClassFileDeclarations(classes::get);
    }

    /**
     * {@code source} compiled against the module's classes and instantiated from a loader of its own.
     *
     * <p>The classes go to a directory rather than a map because that is what makes the loader answer
     * for its own resources: what an implementation's declarations are read from is the class files
     * its loader has, and a loader that serves classes and not resources would leave the reading with
     * nothing to read.
     */
    private static Object builtElsewhere(Map<String, byte[]> generated, String source)
            throws Exception {
        Path classes = Files.createTempDirectory("souther-bound");
        for (Map.Entry<String, byte[]> e : generated.entrySet()) {
            Path at = classes.resolve(e.getKey().replace('.', '/') + ".class");
            Files.createDirectories(at.getParent());
            Files.write(at, e.getValue());
        }
        Path java = classes.resolve("example/todo/FindTodoImpl.java");
        Files.writeString(java, source);
        int rc = ToolProvider.getSystemJavaCompiler().run(null, null, null,
                "-encoding", "UTF-8",
                "-classpath", classes + File.pathSeparator + System.getProperty("java.class.path"),
                "-d", classes.toString(), java.toString());
        assertEquals(0, rc, "the implementation compiles against the module's classes");

        // Its own loader, and the module's classes in it: the base it extends is this loader's and
        // not the run's, which is the whole of what a supplied implementation is.
        URLClassLoader loader = new URLClassLoader(new URL[] {classes.toUri().toURL()},
                ExampleVerifier.class.getClassLoader());
        return loader.loadClass("example.todo.FindTodoImpl").getConstructor().newInstance();
    }
}
