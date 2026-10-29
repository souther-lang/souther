package souther.cli;

import souther.cli.CliProcess.Ran;
import souther.compiler.diag.SourcePos;
import souther.compiler.examples.Deadline;
import souther.compiler.execute.jvm.JvmDeadlines;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A list newtype that states a uniqueness and then a size is a model like any other: the commands
 * that load its decoder answer about its rows, and a generated class the JVM refuses to link is the
 * compiler's own failure, said as one.
 */
class AListWithAUniquenessBeforeASizeIsMeasuredWithoutAnInternalErrorTest {

    private static final String MODEL = """
            module repro

            data Pin = Int
                invariant value >= 1 && value <= 12

            data Pins = List<Pin>
                invariant distinct = List.allDistinctBy(p -> p, value)
                invariant atMost = List.length(value) <= 12

            data Throw = Pins | Fault

            behavior points : (t: Throw) -> Int

            let points (t) =
                match t with
                    | Fault -> 0
                    | Pins as p -> List.length(p.value)

            example points
                | (Pins([Pin(1), Pin(2)])) -> 2

            behavior total : (ts: List<Throw>) -> Int

            let total (ts) = List.fold((acc, t) -> acc + points(t), 0, ts)
            """;

    @Test
    void examplesLoadsTheDecoderAndAnswersAboutTheRows() throws Exception {
        Ran ran = CliInProcess.run("examples", written().toString());

        assertEquals(0, ran.code(), ran.err());
        assertSaysNothingOfLinking(ran);
    }

    @Test
    void generatingRowsLoadsTheDecoderAndAnswersAboutTheRows() throws Exception {
        Ran ran = CliInProcess.run("examples", "--generate", written().toString());

        assertEquals(0, ran.code(), ran.err());
        assertSaysNothingOfLinking(ran);
        assertTrue(ran.out().contains("Pins("), "a row that writes the list: " + ran.out());
    }

    @Test
    void aGeneratedClassThatDoesNotLinkEndsTheCommandAsAnInternalError() {
        ByteArrayOutputStream captured = new ByteArrayOutputStream();
        PrintStream err = new PrintStream(captured, true, StandardCharsets.UTF_8);

        // Thrown by the worker a reading is given, which is where everything a fake table's
        // evaluation ends with arrives.
        int code = Main.guarded(err, () -> {
            JvmDeadlines.of(Duration.ofSeconds(30)).given(
                    new Deadline.Work.Table("fake", new SourcePos(1, 1)), () -> {
                        throw new VerifyError("Bad type on operand stack");
                    });
            return 0;
        });

        String said = captured.toString(StandardCharsets.UTF_8);
        assertEquals(1, code);
        assertTrue(said.contains("internal compiler error"), said);
        assertTrue(said.contains("VerifyError"), "what the JVM said is kept: " + said);
    }

    /** The JVM verifies a class as it loads it, so the failure arrives from loading and not from a
     * call, where nothing wraps it. */
    @Test
    void aBehaviorClassTheJvmWillNotVerifyEndsRunAsAnInternalError() {
        ByteArrayOutputStream captured = new ByteArrayOutputStream();
        PrintStream err = new PrintStream(captured, true, StandardCharsets.UTF_8);

        int code = Main.guarded(err, () -> {
            Runner.invoke(failingToLoad(new VerifyError("Bad type on operand stack")),
                    "repro", "points", new Object[0]);
            return 0;
        });

        String said = captured.toString(StandardCharsets.UTF_8);
        assertEquals(1, code);
        assertTrue(said.contains("internal compiler error"), said);
        assertTrue(said.contains("VerifyError"), said);
    }

    /** What is not the compiler's output is the behavior not running, and says so as it does. */
    @Test
    void aBehaviorClassWhoseInitializerThrewIsTheBehaviorFailing() {
        Runner.RunException failed = assertThrows(Runner.RunException.class,
                () -> Runner.invoke(failingToLoad(new ExceptionInInitializerError(
                        new IllegalStateException("a static that did not hold"))),
                        "repro", "points", new Object[0]));

        String said = failed.localized(Locale.ENGLISH);
        assertTrue(said.contains("`points` failed"), said);
        assertTrue(said.contains("a static that did not hold"), "what it threw is kept: " + said);
    }

    private static ClassLoader failingToLoad(LinkageError failure) {
        return new ClassLoader() {
            @Override
            protected Class<?> loadClass(String name, boolean resolve) {
                throw failure;
            }
        };
    }

    private static void assertSaysNothingOfLinking(Ran ran) {
        String said = ran.out() + ran.err();
        assertFalse(said.contains("VerifyError"), said);
        assertFalse(said.contains("internal compiler error"), said);
        assertFalse(said.contains("would not link"), said);
    }

    private static Path written() throws Exception {
        Path file = Files.createTempDirectory("souther-pins").resolve("both.sou");
        Files.writeString(file, MODEL);
        return file;
    }
}
