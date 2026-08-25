package souther.compiler.execute;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

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
 * <p>What is refused is what #971 refuses: how this compiler answers its own questions, what it
 * emits with, and what it emits. Not {@code souther.compiler.examples} — a {@code Deadline} and an
 * {@code EvaluationPolicy} are declared there and neither is a word of the machine, so refusing the
 * package would be this test making a claim the issue does not, and the stand-in would pass it by
 * not reading the budget rather than by not needing the machine. Whether those two are still owned
 * by the package the JVM implementation runs out of is a question about ownership, and it is not
 * settled by what a test finds convenient.
 */
class AnExecutionThatIsNotTheJvmsCanBeWrittenTest {

    /** How this compiler answers its own questions, what it emits with, and what one execution of a
     *  program runs it as. */
    private static final List<String> THE_MACHINES = List.of(
            "souther.compiler.query",
            "souther.compiler.codegen",
            "souther.compiler.generated",
            "souther.compiler.jvm",
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
}
