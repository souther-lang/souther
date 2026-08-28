package souther.compiler.execute;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Compilation;
import souther.compiler.query.ExampleExecutions;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The other half of the boundary, and the half a walk cannot answer.
 *
 * <p>{@code NothingCrossingTheExecutionBoundaryIsTheMachinesTest} asks what the types say. This asks
 * whether the boundary can be met: {@link RecordingExecution} answers every question the language
 * asks and knows nothing about how a Souther program is run, and it compiles. A boundary that is
 * clean by reflection and cannot be implemented without the machine would be clean and useless.
 *
 * <p>Most of the claim is javac's. Every method of that file carries {@code @Override}, so a
 * question added to {@link ProgramExecution} that cannot be answered from there stops the build. What
 * is left for this to hold is what an import would let through quietly.
 *
 * <p>What is refused is how this compiler answers its own questions, what it emits with, what it
 * emits, and the subsystem that runs a row on a JVM worker. The last of those is refused because
 * what a run is held to and how a run is held to it are two things: the terms are the compile's and
 * cross as {@link EvaluationPolicy}, while the arrangement that keeps them — a thread, a stack, a
 * wall clock, work handed back to the caller — is one implementation's and does not cross at all.
 *
 * <p>Which is why the stand-in reads the terms rather than holding them. A file that took the
 * budget and printed it would satisfy a rule about imports while showing nothing: what the rule is
 * for is an execution that can be held to what the compile decided, and being held to a number
 * means computing with it.
 */
class AnExecutionThatIsNotTheJvmsCanBeWrittenTest {

    /** How this compiler answers its own questions, what it emits with, what one execution of a
     *  program runs it as, and the arrangement that runs a row on a worker of this compile's own. */
    private static final List<String> THE_MACHINES = List.of(
            "souther.compiler.query",
            "souther.compiler.codegen",
            "souther.compiler.generated",
            "souther.compiler.jvm",
            "souther.compiler.examples",
            "ClassLoader");

    private static final Path STAND_IN =
            Path.of("src/test/java/souther/compiler/execute/RecordingExecution.java");

    @Test
    void anExecutionThatIsNotTheJvmsNamesNoneOfIt() throws IOException {
        String written = Files.readString(STAND_IN);
        List<String> naming = new ArrayList<>();
        for (String machine : THE_MACHINES) {
            if (written.contains(machine)) {
                naming.add(machine);
            }
        }

        assertEquals(List.of(), naming,
                "answering the language's questions should not need any of these; if it does, the"
                        + " boundary is asked or answered in the machine's words");
    }

    /**
     * And the file this reads is the one that implements it.
     *
     * <p>A path that had gone stale would read nothing and find nothing in it, which is what a file
     * naming none of the machine looks like. It has happened to a rule with a path in it before.
     */
    @Test
    void andTheStandInIsWhatItSaysItIs() throws IOException {
        String written = Files.readString(STAND_IN);

        assertTrue(written.contains("implements ProgramExecution"),
                () -> STAND_IN + " is not an execution");
        long answered = written.lines().filter(line -> line.strip().equals("@Override")).count();
        assertEquals(ProgramExecution.class.getMethods().length, answered,
                "every question the boundary asks is answered in the stand-in, and each of them"
                        + " under an @Override of its own, so that a question added later cannot be"
                        + " missed");
    }

    /** And it can be asked, in the language's words, by something holding nothing else. */
    @Test
    void andItReadsTheQuestionInTheLanguagesWords() {
        RecordingExecution execution = new RecordingExecution();

        ConstantOutcome answered = execution.check(new ConstantConstruction(
                "example.money", "金額", null, new WrittenValue.Whole(500), List.of(), null));

        assertEquals(new ConstantOutcome.NotEvaluatedHere(), answered);
        assertEquals(List.of("constant 金額 written in example.money at null, of null,"
                        + " over 0 clauses, of Whole[value=500]"),
                execution.asked());
    }

    /** Two behaviors with an {@code example} of their own, so a budget split over what the reading
     *  holds is a different number from the budget. What the reading counts is the blocks and not
     *  the lines in them, which is why one row each is enough and two under one block would not be. */
    private static final String TWO_EXAMPLES = """
            module example.terms
            data N = Int
            data Out = Int
            behavior twice : (n: N) -> Out constructs Out
            let twice (n) = Out(n.value * 2)
            example twice
              | "twice one": (N(1)) -> Out(2)
            behavior thrice : (n: N) -> Out constructs Out
            let thrice (n) = Out(n.value * 3)
            example thrice
              | "thrice one": (N(1)) -> Out(3)
            """;

    /**
     * And what it answers is decided by the terms it was handed.
     *
     * <p>The other tests here say the boundary can be declared and taken without the machine. This
     * says the one part of it that is a term rather than a fact — what the compile holds a run to —
     * arrives as a number an execution can be held to. A stand-in that only carried it would pass
     * every other test in this file, so what this asks is that the answer moves when the terms do:
     * two thousand steps over two examples is a thousand each, and four thousand is two thousand.
     *
     * <p>Which is also why the arrangement that keeps the terms is not here to be read. Whether a
     * budget is kept by a worker and a clock or by something else is the implementation's, and this
     * execution keeps it by dividing it, which is an arrangement too.
     */
    @Test
    void andWhatItAnswersFollowsTheTermsItWasGiven() {
        RecordingExecution execution = new RecordingExecution();

        execution.statements(readingHeldTo(EvaluationPolicy.of(2_000L)));
        execution.statements(readingHeldTo(EvaluationPolicy.of(4_000L)));

        assertEquals(List.of("1000 steps an example", "2000 steps an example"),
                execution.asked().stream().map(AnExecutionThatIsNotTheJvmsCanBeWrittenTest::steps)
                        .toList());
    }

    /**
     * And the wait it is told is the wait this compilation is run on.
     *
     * <p>A budget in milliseconds is what a caller says when it wants a row given up on sooner than
     * a build would. Said as an input of its own it was kept by the JVM and unknown to the boundary,
     * so an execution asked what it was held to answered the default minute while the run it was
     * answering for was already being abandoned at five milliseconds — the boundary stating one
     * thing and the implementation doing another, which is the whole of what this file is about.
     *
     * <p>So it is not an input of its own. It is the wait among the terms, and this reads it back
     * where every execution reads it.
     */
    @Test
    void andTheWaitItIsToldIsTheWaitTheCompilationRunsOn() {
        RecordingExecution execution = new RecordingExecution();

        execution.statements(readingHeldTo(EvaluationPolicy.DEFAULT, Duration.ofMillis(1_234)));

        assertEquals(List.of("given up on after 1234ms"),
                execution.asked().stream().map(AnExecutionThatIsNotTheJvmsCanBeWrittenTest::waited)
                        .toList());
    }

    private static final Pattern GIVEN_UP_AFTER = Pattern.compile("given up on after \\d+ms");

    /** What one sentence says the wait is, or the sentence itself where it says nothing. */
    private static String waited(String said) {
        Matcher matched = GIVEN_UP_AFTER.matcher(said);
        return matched.find() ? matched.group() : said;
    }

    private static final Pattern STEPS_EACH = Pattern.compile("\\d+ steps an example");

    /** What one sentence says an example is allowed, or the sentence itself where it says nothing —
     *  which is what a stand-in that stopped reading the terms would leave to compare. */
    private static String steps(String said) {
        Matcher matched = STEPS_EACH.matcher(said);
        return matched.find() ? matched.group() : said;
    }

    /** {@link #TWO_EXAMPLES} as this compiler reads it, under {@code terms}. */
    private static ExampleExecution readingHeldTo(EvaluationPolicy terms) {
        return readingHeldTo(terms, null);
    }

    /** The same, {@code budget} saying the wait the way a caller with a reason to differ says it. */
    private static ExampleExecution readingHeldTo(EvaluationPolicy terms, Duration budget) {
        Compilation compilation = Compilation.ofSource(TWO_EXAMPLES, "Main");
        compilation.withEvaluationPolicy(terms);
        if (budget != null) {
            compilation.withExampleBudget(budget);
        }
        compilation.answerEverything();
        ExampleExecution reading = ExampleExecutions.of(compilation.db(), "example.terms");
        assertTrue(reading != null, "the module has to check for there to be a reading of it");
        return reading;
    }
}
