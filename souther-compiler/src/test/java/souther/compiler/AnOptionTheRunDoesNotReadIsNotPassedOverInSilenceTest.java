package souther.compiler;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An option the run does not read is not passed over in silence.
 *
 * <p>Not that every option written is read — {@code api Option --source String} answers about
 * {@code Option} and drops the option, and says which of the two it read rather than refusing the
 * line. What holds of all of them is the weaker sentence: the line is refused, or the run says what
 * it did not use. What no line gets is the answer it would have got with the option left out.
 *
 * <p>{@code --boundaries} on its own was accepted and answered with the report it would have printed
 * anyway. The flag is read at one place, inside the branch {@code --generate} opens, so a line that
 * wrote it without {@code --generate} set a variable nothing looked at — and a reader who had just
 * been told {@code boundary 0/2} read the unchanged report as an answer about their model rather
 * than as an option that never applied. Silence is the one thing the command line cannot say here,
 * and the same command already holds the opposite standard for {@code --module} and
 * {@code --behavior}: a name that resolves to no subject is a usage error, not a report of nothing.
 *
 * <p>Every command, and not only the ones whose parser thought to ask. {@code doc} and {@code api}
 * read their options by position and had no case for a token they did not expect, so
 * {@code api Option --nope} ran as though it were not there and {@code api --search fold --limit 1}
 * printed every hit.
 */
class AnOptionTheRunDoesNotReadIsNotPassedOverInSilenceTest {

    @TempDir
    Path dir;

    private record Said(int code, String err, String out) {}

    /** Runs the command line and answers with its exit code and what it wrote. */
    private Said run(String... args) {
        PrintStream originalErr = System.err;
        PrintStream originalOut = System.out;
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            int code = Main.dispatch(args);
            return new Said(code, err.toString(StandardCharsets.UTF_8),
                    out.toString(StandardCharsets.UTF_8));
        } finally {
            System.setErr(originalErr);
            System.setOut(originalOut);
        }
    }

    private static final String MODEL = """
            module example.timesheet

            data MinuteOfDay = Int
                invariant withinDay = value >= 0 && value <= 1440

            data Shift =
                { startsAt: MinuteOfDay
                , endsAt: MinuteOfDay
                }
                invariant endsAfterStart = startsAt < endsAt

            data Short
            data Long

            behavior classify : (shift: Shift) -> Short | Long
                constructs Short, Long

            let classify (shift) =
                if shift.endsAt.value - shift.startsAt.value >= 480 then Long else Short

            example classify
                | "short" : (Shift { startsAt = MinuteOfDay(540), endsAt = MinuteOfDay(600) })
                    -> Short
            """;

    private Path model() throws Exception {
        Path file = dir.resolve("timesheet.sou");
        Files.writeString(file, MODEL);
        return file;
    }

    // --- the option that is read behind another one -----------------------------------------------

    @Test
    void boundariesWithoutGenerateIsRefused() throws Exception {
        Said said = run("examples", model().toString(), "--boundaries");

        assertEquals(2, said.code(), said.err());
        assertTrue(said.err().contains("`--boundaries`"), said.err());
        assertTrue(said.err().contains("`--generate`"), said.err());
    }

    /** The refusal comes before the report, so the reader is not shown a measurement to misread. */
    @Test
    void boundariesWithoutGenerateReportsNothing() throws Exception {
        Said said = run("examples", model().toString(), "--boundaries");

        assertEquals("", said.out(), said.out());
    }

    @Test
    void boundariesWithGenerateIsTheLineThatWasMeant() throws Exception {
        Said said = run("examples", model().toString(), "--generate", "--boundaries");

        assertEquals(0, said.code(), said.err());
        assertTrue(said.out().contains("MinuteOfDay(1440)"), said.out());
    }

    /** The order they are written in is not one of the conditions. */
    @Test
    void boundariesBeforeGenerateIsTheSameLine() throws Exception {
        Said said = run("examples", model().toString(), "--boundaries", "--generate");

        assertEquals(0, said.code(), said.err());
        assertTrue(said.out().contains("MinuteOfDay(1440)"), said.out());
    }

    /** {@code doc}'s own conditional option: the limit is read out of the search and nowhere else. */
    @Test
    void limitWithoutSearchIsRefused() {
        Said said = run("doc", "--limit", "5");

        assertEquals(2, said.code(), said.err());
        assertTrue(said.err().contains("`--limit`"), said.err());
        assertTrue(said.err().contains("`--search`"), said.err());
    }

    /**
     * What the option promises, which is that two is how many are shown — not that the answer got
     * shorter, and not how many the specification happens to say the term.
     *
     * <p>Counted in hits. A hit is several lines, the section and the context quoted under it, so
     * counting lines measures how much each one had to say; two hits under either limit print the
     * same text and the comparison holds with the option never read. That is how this passed here
     * and failed on CI. The control says when the question is empty.
     */
    @Test
    void limitWithSearchShowsThatManyHits() {
        Said said = run("doc", "--search", "type", "--limit", "2");
        Said all = run("doc", "--search", "type", "--limit", "0");

        assertEquals(0, said.code(), said.err());
        assertTrue(hits(all) > 2, "a term with no more hits than the limit measures nothing: " + all.out());
        assertEquals(2, hits(said), said.out());
    }

    /**
     * The value that is not there. `--limit` is read inside a loop that skipped it when nothing
     * followed, so this searched under the default and answered as though the option had not been
     * written — the defect this class is about, one option over.
     */
    @Test
    void anOptionWrittenWithoutItsValueIsRefused() {
        Said said = run("doc", "--search", "newtype", "--limit");

        assertEquals(2, said.code(), said.err());
        assertTrue(said.err().contains("`--limit`"), said.err());
        assertEquals("", said.out(), said.out());
    }

    /**
     * Which options take a value is written twice: in the table, where the walk above the dispatch
     * decides whether the token after an option is its value or the next argument, and in the parser
     * that reads it. Nothing makes the two agree, and a disagreement is not a compile error — a
     * parser reading a value the table calls a flag takes the argument after it, and one the table
     * calls valued has its value read as an argument.
     *
     * <p>Asked by writing each option the way the table says it is written, with a source file after
     * it, and looking at what became of the file. The observation does not go through the table: a
     * parser that swallowed the file says it was given none, and one that read the value as a second
     * file says it could not open it. Both are what a disagreement produces, in either direction.
     *
     * <p>Over the commands whose subject is a file. {@code doc}, {@code api} and {@code japi} read
     * their arguments by position rather than in a loop, so {@code --search}, {@code --limit} and
     * {@code --source} are outside this and are held by the cases written out above.
     */
    @Test
    void theTableAndTheParsersAgreeOnWhichOptionsTakeAValue() throws Exception {
        Path out = dir.resolve("out");
        Path empty = Files.createDirectories(dir.resolve("empty"));
        Path formatted = canonical();
        for (String option : Main.knownOptions()) {
            String owner = Main.optionOwners(option).split("/")[0];
            if (!List.of("compile", "examples", "fmt").contains(owner)) {
                continue;
            }
            String value = valueFor(option, empty, out);
            assertEquals(CliOption.takesValue(option), value != null,
                    option + ": this test has no value to write for an option that takes one");

            List<String> line = new ArrayList<>(List.of(owner));
            if (owner.equals("compile")) {
                line.addAll(List.of("-d", out.toString()));
            }
            if (option.equals("--boundaries")) {
                line.add("--generate");   // which it is only read with
            }
            line.add(option);
            if (value != null) {
                line.add(value);
            }
            line.add(formatted.toString());

            Said said = run(line.toArray(String[]::new));

            assertFalse(said.err().contains("at least one .sou file"),
                    line + ": the file was read as this option's value: " + said.err());
            assertFalse(said.err().contains("io error"),
                    line + ": this option's value was read as a file: " + said.err());
            assertFalse(said.err().contains("unknown option"), line + ": " + said.err());
        }
    }

    /** What to write after the option, or null where the table says it takes nothing. */
    private String valueFor(String option, Path empty, Path out) {
        return switch (option) {
            case "--format" -> "human";
            case "--lang" -> "en";
            case "--color" -> "never";
            case "--adequacy" -> "off";
            case "--warnings" -> "report";
            case "--module" -> "example.timesheet";
            case "--behavior" -> "classify";
            case "-cp", "--class-path" -> empty.toString();
            case "-d" -> out.toString();
            default -> null;
        };
    }

    /** The model in the form `fmt --check` accepts, so that probing `--check` says nothing about
     *  how the file happened to be written here. */
    private Path canonical() throws Exception {
        Path file = model();
        assertEquals(0, run("fmt", "-w", file.toString()).code());
        return file;
    }

    /** What the search answered, without the lines quoted under each one or the count of the rest. */
    private static long hits(Said said) {
        return said.out().lines()
                .filter(line -> !line.startsWith("    ") && !line.startsWith("… "))
                .count();
    }

    /**
     * Every option the table says needs another, asked of a command that takes it — so a pair added
     * tomorrow is under this without anything here being written again.
     *
     * <p>Beside the two written out above rather than instead of them. This reads the same table the
     * check reads, so a pair the table is missing is a pair it does not ask about: dropping
     * {@code --boundaries} from the relation leaves this passing over one fewer option and saying
     * nothing. The named cases are what holds each of those two rows down.
     */
    @Test
    void everyOptionThatNeedsAnotherIsRefusedWithoutIt() {
        for (String option : Main.knownOptions()) {
            String needed = CliOption.needed(option);
            if (needed == null) {
                continue;
            }
            String owner = Main.optionOwners(option).split("/")[0];
            // With its value, so that what this reads is the option it is missing and not the value
            // it is missing — an option written last is refused for that first.
            Said said = CliOption.takesValue(option)
                    ? run(owner, option, "1") : run(owner, option);

            assertEquals(2, said.code(), option + ": " + said.err());
            assertTrue(said.err().contains("`" + needed + "`"),
                    option + " needs " + needed + ": " + said.err());
        }
    }

    // --- the two that may not be written together -------------------------------------------------

    @Test
    void everyExclusivePairIsRefusedTogether() throws Exception {
        for (List<String> pair : CliOption.exclusive()) {
            String owner = Main.optionOwners(pair.get(0)).split("/")[0];
            Said said = run(owner, model().toString(), pair.get(0), pair.get(1));

            assertEquals(2, said.code(), pair + ": " + said.err());
            assertTrue(said.err().contains("`" + pair.get(0) + "`"), pair + ": " + said.err());
            assertTrue(said.err().contains("`" + pair.get(1) + "`"), pair + ": " + said.err());
        }
    }

    /** The refusal names the option the way the line wrote it, not the way the table lists it. */
    @Test
    void anOptionIsNamedAsItWasWritten() throws Exception {
        Said said = run("fmt", model().toString(), "--write", "--check");

        assertEquals(2, said.code(), said.err());
        assertTrue(said.err().contains("`--write`"), said.err());
        assertFalse(said.err().contains("`-w`"), said.err());
    }

    // --- the commands that were not asking ---------------------------------------------------------

    /**
     * {@code api} reads its options by position, so a token it did not expect fell through to the
     * name it was asked about and the run went on.
     */
    @Test
    void aCommandThatReadsByPositionRefusesAnUnknownOption() {
        Said said = run("api", "Option", "--nope");

        assertEquals(2, said.code(), said.err());
        assertTrue(said.err().contains("unknown option `--nope`"), said.err());
        assertEquals("", said.out(), said.out());
    }

    /** An option that exists and is another command's, asked of a command that reads by position. */
    @Test
    void aCommandThatReadsByPositionRefusesAnotherCommandsOption() {
        Said said = run("api", "--search", "fold", "--limit", "1");

        assertEquals(2, said.code(), said.err());
        assertTrue(said.err().contains("unknown option `--limit`"), said.err());
        assertTrue(said.err().contains("it is an option of doc"), said.err());
        assertEquals("", said.out(), said.out());
    }

    @Test
    void docRefusesAnUnknownOption() {
        Said said = run("doc", "--nope");

        assertEquals(2, said.code(), said.err());
        assertTrue(said.err().contains("unknown option `--nope`"), said.err());
    }

    @Test
    void japiRefusesAnUnknownOption() {
        Said said = run("japi", "java.lang.String", "--nope");

        assertEquals(2, said.code(), said.err());
        assertTrue(said.err().contains("unknown option `--nope`"), said.err());
    }

    /** What each of those commands does with a line of its own is untouched. */
    @Test
    void aCommandThatReadsByPositionStillAnswers() {
        Said said = run("api", "--search", "fold");

        assertEquals(0, said.code(), said.err());
        assertTrue(said.out().contains("List.fold"), said.out());
    }

    /**
     * An option of the command's own, written where the command does not read it. The check above
     * the dispatch passes it — it is {@code api}'s option, written with the value {@code api} takes
     * — and the command answers the front of the line. Which one it read is what {@code doc} says of
     * the same line, and is what tells the reader the rest of what they wrote did not apply.
     */
    @Test
    void aCommandThatReadsByPositionSaysWhichQuestionItAnswered() {
        Said said = run("api", "Option", "--source", "String");

        assertEquals(0, said.code(), said.err());
        assertTrue(said.err().contains("reading `Option`"), said.err());
        assertTrue(said.err().contains("--source"), said.err());
        assertTrue(said.out().contains("Option.map"), said.out());
    }

    /** And says nothing where the line asked for one thing. */
    @Test
    void aLineThatAsksForOneThingIsAnsweredWithoutANote() {
        Said said = run("api", "--source", "String");

        assertEquals(0, said.code(), said.err());
        assertFalse(said.err().contains("reads one at a time"), said.err());
    }

    // --- what a value is ---------------------------------------------------------------------------

    /**
     * A value spelt like an option is a value. The check walks the line the way the parsers do, so
     * a module named {@code --generate} is the module the command was asked about — a wrong name,
     * answered as one — and not an option that arrived twice.
     */
    @Test
    void aValueSpeltLikeAnOptionIsAValue() throws Exception {
        Said said = run("examples", model().toString(), "--module", "--generate", "--boundaries");

        assertEquals(2, said.code(), said.err());
        assertTrue(said.err().contains("`--boundaries`"), said.err());
        assertTrue(said.err().contains("`--generate`"), said.err());
    }

    /** A short option a command does not know still reads as a path, which is the older rule. */
    @Test
    void aShortOptionAnotherCommandOwnsIsStillAPath() throws Exception {
        Said said = run("compile", model().toString(), "-d", dir.resolve("out").toString(), "-w");

        assertNotEquals(2, said.code(), said.err());
        assertFalse(said.err().contains("unknown option"), said.err());
    }

    /**
     * And is not passed on to a command with nowhere to put it. Reading an unknown short token as an
     * operand is what every other command does with it; {@code mcp} has no operand, read none of
     * what it was handed, and served as though the line had been written on its own.
     */
    @Test
    void aCommandWithNoOperandRefusesWhatItWouldNotRead() {
        Said said = run("mcp", "-w");

        assertEquals(2, said.code(), said.err());
        assertTrue(said.err().contains("`souther mcp`"), said.err());
        assertTrue(said.err().contains("-w"), said.err());
    }

    /** A path is not an operand of it either. */
    @Test
    void aCommandWithNoOperandRefusesAPathToo() {
        Said said = run("mcp", "model.sou");

        assertEquals(2, said.code(), said.err());
        assertTrue(said.err().contains("model.sou"), said.err());
    }

    /** And an option nobody has is still refused above it, as it was. */
    @Test
    void aCommandWithNoOperandStillRefusesAnUnknownOption() {
        Said said = run("mcp", "--nope");

        assertEquals(2, said.code(), said.err());
        assertTrue(said.err().contains("unknown option `--nope`"), said.err());
    }

    // --- the language the refusal is written in ----------------------------------------------------

    /**
     * Read off the same line it refuses. The command line resolves the language in one place and
     * every answer it gives is in that language; a refusal raised before the subcommand parses is
     * still one of its answers.
     */
    @Test
    void aRefusalIsWrittenInTheLanguageTheLineAsksFor() throws Exception {
        Said said = run("examples", model().toString(), "--boundaries", "--lang", "ja");

        assertEquals(2, said.code(), said.err());
        assertTrue(said.err().contains("`--boundaries`"), said.err());
        assertFalse(said.err().contains("is only read with"), said.err());
    }
}
