package souther.compiler.examples;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;
import souther.compiler.observe.FailurePhase;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import javax.tools.ToolProvider;

import java.io.File;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A bound implementation held to what the behavior states, and to nothing the row records.
 *
 * <p>A row carries inputs and a recorded answer, and until now the only question that could be asked
 * of an implementation was whether it answered the value somebody wrote. What the model
 * <em>states</em> — the {@code ensures} — could not be asked on its own, though it is the oracle a
 * contract test wants: the rows supply the inputs, the declaration decides the answers.
 *
 * <p>The two oracles part inside one world as readily as across two, which is what
 * {@link #anAnswerTheRecordDoesNotHaveCanStillKeepWhatIsDeclared} holds. Where they part in practice
 * is a world the rows were not recorded in — a shared database, a snapshot — and there the recorded
 * answer is no longer the answer while the declaration still is.
 */
class AnImplementationIsHeldToTheDeclarationAndNotToTheRecordTest {

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

    /** The same model, stating a relation between what it is given and what it answers. */
    private static final String DECLARING = declaring("value.id.value == id.value");

    /** Answers both rows the way the model records them. */
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

    /**
     * Answers the stored id with another title.
     *
     * <p>The clause says nothing about the title, so this keeps what the behavior states and answers
     * something the row does not record. That is the pair the two oracles disagree on.
     */
    private static final String ANOTHER_TITLE = """
            package example.todo;
            public final class FindTodoImpl extends FindTodo {
                public FindTodoResult apply(TodoId id) {
                    return id.equals(new TodoId(1L))
                            ? new Todo(new TodoId(1L), new Title("read the SQL"), false)
                            : new NotFound(id);
                }
            }
            """;

    /** Answers the stored row with a todo carrying an id nobody asked for. */
    private static final String ANOTHER_ID = """
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
     * Answers within the clause once and outside it after.
     *
     * <p>A world that changed between two asks, which is the position every caller of this face is
     * in: the rows are asked in whatever state the caller arranged, and this is that state written
     * as the implementation rather than as a database.
     */
    private static final String ONCE_THEN_NOT = """
            package example.todo;
            public final class FindTodoImpl extends FindTodo {
                private int asked = 0;
                public FindTodoResult apply(TodoId id) {
                    long answer = asked++ == 0 ? id.value() : 7L;
                    return new Todo(new TodoId(answer), new Title("write the SQL"), false);
                }
            }
            """;

    /** Applying it is the failure. Bound where nothing may apply it, it says so by never running. */
    private static final String REFUSES = """
            package example.todo;
            public final class FindTodoImpl extends FindTodo {
                public FindTodoResult apply(TodoId id) {
                    throw new IllegalStateException("this implementation must not be applied");
                }
            }
            """;

    /**
     * The fact the face exists for: one answer, two oracles, and they disagree.
     *
     * <p>{@code evaluate} refuses the row because the title is not the one written out.
     * {@code checkContract} is told nothing about the title — the behavior states nothing about it —
     * and answers that no clause was broken. Neither is wrong; they are two questions.
     */
    @Test
    void anAnswerTheRecordDoesNotHaveCanStillKeepWhatIsDeclared() throws Exception {
        BoundExamples bound = boundTo(DECLARING, ANOTHER_TITLE);
        RecordedRow stored = named(bound, "a todo that is stored");

        RowEvaluation evaluated = bound.evaluate(stored);
        assertFalse(evaluated.held(), "the recorded oracle refuses it");
        assertEquals(FailurePhase.COMPARISON, evaluated.outcome().failurePhase());

        assertInstanceOf(ContractObservation.NoClauseWasBroken.class, bound.checkContract(stored),
                "and the declared oracle does not, the clause saying nothing about a title");
    }

    /** The control: what the record and the declaration both admit is admitted by both. */
    @Test
    void anAnswerBothOraclesAdmitIsAdmittedByBoth() throws Exception {
        BoundExamples bound = boundTo(DECLARING, ANSWERS);
        for (RecordedRow row : bound.rows()) {
            assertTrue(bound.evaluate(row).held(), row.shown());
            assertInstanceOf(ContractObservation.NoClauseWasBroken.class,
                    bound.checkContract(row), row.shown());
        }
    }

    /** A clause that does not hold, said with what broke it. */
    @Test
    void aClauseThatDoesNotHoldSaysSoAndSaysWhatWasAnswered() throws Exception {
        BoundExamples bound = boundTo(DECLARING, ANOTHER_ID);

        ContractObservation seen = bound.checkContract(named(bound, "a todo that is stored"));
        ContractObservation.Broken broken =
                assertInstanceOf(ContractObservation.Broken.class, seen);
        assertFalse(broken.why().isBlank(), "the clause said something about not holding");

        // Written the way a fixture writes a value, which is what tells a reader that the id wears
        // `TodoId` rather than being a number that happens to be seven. The value's own `toString`
        // says neither, and is what an arm with no declarations in reach would be left with.
        assertEquals("Todo { done = false, id = TodoId(7), title = Title(\"write the SQL\") }",
                broken.shownAnswered());
        assertTrue(seen.shown().contains(broken.shownAnswered()),
                "and it is what a suite would print: " + seen.shown());
        assertInstanceOf(souther.compiler.observe.ObservedValue.Constructed.class, broken.answered(),
                "beside the value itself, which is what a machine reads");
    }

    /**
     * A behavior that states nothing is answered without the implementation being applied.
     *
     * <p>An arm rather than a quiet yes: a suite over such a behavior would otherwise be green while
     * asserting that a call did not throw. That the implementation is not applied is measured and not
     * asserted about — this one throws when applied, so an answer that is not {@code Unobserved} is
     * the evidence.
     */
    @Test
    void aBehaviorStatingNothingHoldsAnImplementationToNothingAndIsNotApplied() throws Exception {
        BoundExamples bound = boundTo(MODEL, REFUSES);

        ContractObservation seen = bound.checkContract(bound.rows().get(0));
        ContractObservation.NothingStated stated =
                assertInstanceOf(ContractObservation.NothingStated.class, seen,
                        "an implementation that throws when applied was not applied");
        assertEquals("findTodo", stated.behavior());
        assertTrue(seen.shown().contains("findTodo"));
    }

    /**
     * A binding nothing may be handed to is said as that, and not as the model stating nothing.
     *
     * <p>Both are true of this row: the implementation is of a build whose {@code Title} admits
     * values this one does not, and the model states nothing. Answering the second would send its
     * author to write a clause that would still not run, so the binding is answered for first.
     */
    @Test
    void anImplementationOfAnotherBuildIsSaidAsThatEvenWhereNothingIsStated() throws Exception {
        String narrowed = MODEL.replace("    invariant length(value) > 0\n",
                "    invariant length(value) > 3\n");
        BoundExamples bound = SoutherExamples.ofSource(narrowed)
                .bind(builtElsewhere(compiled(MODEL), ANSWERS));

        ContractObservation seen = bound.checkContract(bound.rows().get(0));
        ContractObservation.Unobserved unobserved =
                assertInstanceOf(ContractObservation.Unobserved.class, seen);
        assertInstanceOf(StandinObservation.Reason.TheImplementationIsOfAnotherBuild.class,
                unobserved.why());
    }

    /**
     * The same row asked twice under two worlds is two observations.
     *
     * <p>What this face is for is asking a row where the world is not the one it was recorded in, so
     * a caller asks the same row again after arranging something else. Nothing may be carried from
     * the first ask to the second: an observation kept would answer about a world that is gone.
     *
     * <p>Measured rather than reasoned from the code that builds a fixture reader per call — that is
     * why it holds today, and this is what says it still does.
     */
    @Test
    void theSameRowAskedTwiceIsAskedAfreshEachTime() throws Exception {
        BoundExamples bound = boundTo(DECLARING, ONCE_THEN_NOT);
        RecordedRow stored = named(bound, "a todo that is stored");

        assertInstanceOf(ContractObservation.NoClauseWasBroken.class, bound.checkContract(stored),
                "the world as it stood for the first ask");
        assertInstanceOf(ContractObservation.Broken.class, bound.checkContract(stored),
                "and as it stood for the second, which is not the first answered again");
    }

    /** Which behaviors state something, answered from the declaration and without applying one. */
    @Test
    void whichBehaviorsStateSomethingIsAskedOfTheModel() throws Exception {
        assertEquals(List.of(), boundTo(MODEL, REFUSES).behaviorsStatingContracts(),
                "nothing is stated, so a suite meaning to hold contracts holds none of these rows");
        assertEquals(List.of("findTodo"), boundTo(DECLARING, REFUSES).behaviorsStatingContracts());
    }

    /**
     * The premise this face rests on: a model whose contract could not be read never gets here.
     *
     * <p>{@code Bodies.Contracts} leaves out a behavior whose clause it could not read, the same way
     * it leaves out one that states nothing — so inside {@code BoundExamples} the two would be one
     * answer, and a row would be told the behavior states nothing when what it states was
     * unreadable. What keeps them apart is the entrance: a model that does not compile makes no
     * {@code SoutherExamples}, and a clause naming what denotes nothing does not compile.
     *
     * <p>Held here rather than left to the reading of one call site, because it is what makes
     * {@link ContractObservation.NothingStated} mean what it says. If the entrance is ever loosened,
     * this is what says the premise went with it.
     */
    @Test
    void aModelWhoseClauseCannotBeReadMakesNoBoundExamples() {
        // `Bodies.Contracts` gives a behavior up in two ways, and both leave it out of the contracts
        // exactly as a behavior that states nothing is left out. Both arms are held, because either
        // one reaching `BoundExamples` would be reported as `NothingStated`.

        // `Unanswerable`: the clause rests on a name that denotes nothing. It carries no diagnostic
        // of its own — the name was reported where it was written — so what refuses the model is
        // that report.
        CompileException named = assertThrows(CompileException.class, () ->
                        SoutherExamples.ofSource(declaring("value.id.value == nobodyDeclaredThis(id)")),
                "a clause resting on a name that denotes nothing");
        assertFalse(named.diagnostics().isEmpty(), "the name was reported where it was written");

        // `CompileException`: the clause is read and refused. `BehaviorChecker` raises E1619 inside
        // `contractOf`, and `Bodies.Contracts` files it as a report rather than raising.
        CompileException refused = assertThrows(CompileException.class,
                () -> SoutherExamples.ofSource(MODEL.replace(
                        "behavior findTodo : (id: TodoId) -> Todo | NotFound\n",
                        """
                        behavior findTodo : (id: TodoId) -> Todo | NotFound
                            ensures Title -> value.id.value == id.value
                        """)),
                "an arm that is not a case of what the behavior answers");
        assertEquals(List.of("E1619"),
                refused.diagnostics().stream().map(souther.compiler.diag.Diagnostic::code).distinct().toList());
    }

    /** {@link #MODEL} with one clause written on {@code findTodo}. */
    private static String declaring(String clause) {
        return MODEL.replace(
                "behavior findTodo : (id: TodoId) -> Todo | NotFound\n",
                "behavior findTodo : (id: TodoId) -> Todo | NotFound\n"
                        + "    ensures Todo -> " + clause + "\n");
    }

    // --- harness ---------------------------------------------------------------------------------

    private static BoundExamples boundTo(String model, String implementation) throws Exception {
        return SoutherExamples.ofSource(model).bind(builtElsewhere(compiled(model), implementation));
    }

    private static RecordedRow named(BoundExamples bound, String name) {
        return bound.rows().stream()
                .filter(row -> row.shown().equals(name))
                .findFirst()
                .orElseThrow(() -> new AssertionError("no row named `" + name + "`"));
    }

    private static Map<String, byte[]> compiled(String model) {
        return Compilation.ofSource(model, "Main").db().ask(new Output.All()).value();
    }

    private static Object builtElsewhere(Map<String, byte[]> generated, String source)
            throws Exception {
        Path classes = Files.createTempDirectory("souther-contract");
        for (Map.Entry<String, byte[]> e : generated.entrySet()) {
            Path at = classes.resolve(e.getKey().replace('.', '/') + ".class");
            Files.createDirectories(at.getParent());
            Files.write(at, e.getValue());
        }
        Path java = classes.resolve("example/todo/FindTodoImpl.java");
        Files.createDirectories(java.getParent());
        Files.writeString(java, source);
        int rc = ToolProvider.getSystemJavaCompiler().run(null, null, null,
                "-encoding", "UTF-8",
                "-classpath", classes + File.pathSeparator + System.getProperty("java.class.path"),
                "-d", classes.toString(), java.toString());
        assertEquals(0, rc, "the implementation compiles against the module's classes");
        URLClassLoader loader = new URLClassLoader(new URL[] {classes.toUri().toURL()},
                ExampleVerifier.class.getClassLoader());
        return loader.loadClass("example.todo.FindTodoImpl").getConstructor().newInstance();
    }
}
