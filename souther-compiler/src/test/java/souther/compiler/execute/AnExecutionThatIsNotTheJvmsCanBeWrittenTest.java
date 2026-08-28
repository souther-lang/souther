package souther.compiler.execute;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Compilation;
import souther.compiler.query.ExampleExecutions;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
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

    /** Two behaviors with rows of their own, so a budget split over what the reading holds is a
     *  different number from the budget. */
    private static final String TWO_ROWS = """
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
     * two thousand steps over two rows is a thousand a row, and four thousand is two thousand.
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

        assertEquals(List.of("1000 steps a row", "2000 steps a row"),
                execution.asked().stream().map(AnExecutionThatIsNotTheJvmsCanBeWrittenTest::steps)
                        .toList());
    }

    private static final Pattern STEPS_A_ROW = Pattern.compile("\\d+ steps a row");

    /** What one sentence says a row is allowed, or the sentence itself where it says nothing —
     *  which is what a stand-in that stopped reading the terms would leave to compare. */
    private static String steps(String said) {
        Matcher matched = STEPS_A_ROW.matcher(said);
        return matched.find() ? matched.group() : said;
    }

    /** {@link #TWO_ROWS} as this compiler reads it, under {@code terms}. */
    private static ExampleExecution readingHeldTo(EvaluationPolicy terms) {
        Compilation compilation = Compilation.ofSource(TWO_ROWS, "Main");
        compilation.withEvaluationPolicy(terms);
        compilation.answerEverything();
        ExampleExecution reading = ExampleExecutions.of(compilation.db(), "example.terms");
        assertTrue(reading != null, "the module has to check for there to be a reading of it");
        return reading;
    }
}
