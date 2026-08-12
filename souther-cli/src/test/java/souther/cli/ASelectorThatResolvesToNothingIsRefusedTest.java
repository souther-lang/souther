package souther.cli;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What {@code souther examples --module} and {@code --behavior} do with a name nothing answers to.
 *
 * <p>They used to report on the empty selection they had made, and a report of nothing says the
 * measurement went through and found no gap: {@code status} folded over no modules kept the word it
 * started at, the verdict over no measures was {@code undetermined}, and {@code --strict} lets that
 * through because a measure that was not made is not a gap. Every one of those steps is right about
 * the question it answers. The one that is not asked anywhere is whether the name resolved.
 *
 * <p>So it is asked before a report exists. Whether a selector names a subject is a fact about the
 * command line and what the sources declare, and it is settled against the declarations rather than
 * against what reached the report — a module that was declared and could not be measured is an
 * absent measurement, and refusing the name over it would report the one as the other.
 */
class ASelectorThatResolvesToNothingIsRefusedTest {

    /** A model with a behavior and a gap: without a selector this exits non-zero under
     *  {@code --strict}, which is what a misspelled selector used to hide. */
    private static final String RATE = """
            module example.rate

            data Amount = Int
                invariant value >= 0

            data Charged = { cost: Amount }
            data Refused = { reason: String }

            behavior submit : (cost: Amount) -> Charged | Refused
                constructs Charged, Refused

            let submit (cost) = {
                guard cost.value <= 100 else Refused { reason = "over" }
                Charged { cost = cost }
            }

            example submit
                | "within" : (Amount(50)) -> Charged
            """;

    /** A second module, so that two names can each resolve and still select nothing together. */
    private static final String AUDIT = """
            module example.audit

            data Entry = { what: String }

            behavior record : (what: String) -> Entry
                constructs Entry

            let record (what) = Entry { what = what }

            example record
                | "one" : ("a") -> Entry { what = "a" }
            """;

    /** A module that declares no behavior at all, which is what an empty selection looks like once
     *  the report is made. The name resolves, so this is not the same answer. */
    private static final String NO_BEHAVIOR = """
            module example.empty

            data Amount = Int
                invariant value >= 0
            """;

    @Test
    void aModuleNameNothingDeclaresIsRefusedInsteadOfReportedOn() throws Exception {
        Run run = examples(List.of(RATE), "--module", "example.nosuch", "--strict");

        assertEquals(2, run.code(), run.out() + run.err());
        assertTrue(run.err().contains("example.nosuch"), run.err());
        assertTrue(run.err().contains("example.rate"), run.err());
        assertFalse(run.out().contains("adequacy"), run.out());
    }

    @Test
    void aBehaviorNameNothingDeclaresIsRefusedInsteadOfReportedOn() throws Exception {
        Run run = examples(List.of(RATE), "--behavior", "nosuch", "--strict");

        assertEquals(2, run.code(), run.out() + run.err());
        assertTrue(run.err().contains("nosuch"), run.err());
        assertTrue(run.err().contains("submit"), run.err());
        assertFalse(run.out().contains("adequacy"), run.out());
    }

    /**
     * Two names that each name something, and nothing that is both.
     *
     * <p>Resolving them one at a time would pass this: {@code example.rate} is a module and
     * {@code record} is a behavior. What the command was asked for is the pair, and the pair holds
     * nothing.
     */
    @Test
    void selectorsAreResolvedTogetherAndNotOneAtATime() throws Exception {
        Run run = examples(List.of(RATE, AUDIT),
                "--module", "example.rate", "--behavior", "record", "--strict");

        assertEquals(2, run.code(), run.out() + run.err());
        assertTrue(run.err().contains("record"), run.err());
        assertTrue(run.err().contains("submit"), run.err());
        assertFalse(run.out().contains("adequacy"), run.out());
    }

    /** The gap the misspelled selector used to hide, still refused where the name resolves. */
    @Test
    void aSelectorThatResolvesReportsAndStrictStillRefusesTheGap() throws Exception {
        Run run = examples(List.of(RATE), "--module", "example.rate", "--behavior", "submit",
                "--strict");

        assertEquals(1, run.code(), run.out() + run.err());
        assertTrue(run.out().contains("adequacy: not satisfied"), run.out());
    }

    /**
     * A module that declares no behavior is selected, not refused.
     *
     * <p>This is the case the empty selection was indistinguishable from: the report it produces has
     * the same shape either way. Nothing here was misspelled, so the answer is the report — the same
     * one the command gives with no selector at all.
     */
    @Test
    void aModuleThatDeclaresNoBehaviorResolves() throws Exception {
        Run selected = examples(List.of(NO_BEHAVIOR), "--module", "example.empty", "--strict");
        Run whole = examples(List.of(NO_BEHAVIOR), "--strict");

        assertEquals(0, selected.code(), selected.out() + selected.err());
        assertEquals(whole.out(), selected.out());
    }

    /** A selector naming a module in a compilation of several, with the other left out. */
    @Test
    void oneModuleOfSeveralResolves() throws Exception {
        Run run = examples(List.of(RATE, AUDIT), "--module", "example.audit");

        assertEquals(0, run.code(), run.out() + run.err());
        assertTrue(run.out().contains("example.audit"), run.out());
        assertFalse(run.out().contains("example.rate"), run.out());
    }

    /** A behavior named without a module is looked for across all of them. */
    @Test
    void aBehaviorNameResolvesAgainstEveryModuleWhenNoneIsNamed() throws Exception {
        Run run = examples(List.of(RATE, AUDIT), "--behavior", "record");

        assertEquals(0, run.code(), run.out() + run.err());
        assertTrue(run.out().contains("record"), run.out());
        assertFalse(run.out().contains("submit"), run.out());
    }

    private record Run(int code, String out, String err) {}

    private static Run examples(List<String> models, String... extraArgs) throws Exception {
        Path dir = Files.createTempDirectory("souther-selector");
        List<String> args = new ArrayList<>(List.of("examples"));
        for (int i = 0; i < models.size(); i++) {
            Path file = dir.resolve("m" + i + ".sou");
            Files.writeString(file, models.get(i));
            args.add(file.toString());
        }
        args.addAll(List.of(extraArgs));
        return cli(args.toArray(String[]::new));
    }

    private static Run cli(String... args) {
        PrintStream originalOut = System.out;
        PrintStream originalErr = System.err;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
        int code;
        try {
            code = Main.dispatch(args);
        } finally {
            System.setOut(originalOut);
            System.setErr(originalErr);
        }
        return new Run(code, out.toString(StandardCharsets.UTF_8),
                err.toString(StandardCharsets.UTF_8));
    }
}
