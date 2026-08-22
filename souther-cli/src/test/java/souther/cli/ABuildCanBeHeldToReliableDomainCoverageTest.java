package souther.cli;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;


import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a build is held to is what it asked for, and it is not how much it measured.
 *
 * <p>The levels say what to measure: what separates {@code witness} from {@code all} is a second set
 * of classes and a second run of every row. The points a row is owed away from a line cost nothing
 * extra — they come off the same assessment of the same border as the points against it — so
 * refusing over them is a bar and not a measurement, and there was no way to ask for it. A compile
 * at the highest level exited {@code 0} over a model whose {@code IN} and {@code OUT} points no row
 * was at, which is a question only {@code souther examples} answered (issue #937).
 */
class ABuildCanBeHeldToReliableDomainCoverageTest {

    /**
     * A model whose rows sit on the line and one step over it, and nowhere else.
     *
     * <p>Simplified domain coverage is met and reliable domain coverage is not, which is the whole
     * difference between the two bars.
     */
    private static final String ON_THE_LINE_ONLY = """
            module example.limit

            data Ok
            data TooHigh

            behavior grade : (score: Int) -> Ok | TooHigh

            let grade (score) = {
                guard score <= 100 else TooHigh
                Ok
            }

            example grade
                | "on the line" : (100) -> Ok
                | "a step over" : (101) -> TooHigh
            """;

    @Test
    void theHighestLevelIsNotHeldToThePointsAwayFromTheLine() throws Exception {
        Run compiled = compile(ON_THE_LINE_ONLY, "all");

        assertEquals(0, compiled.code(), compiled.out() + compiled.err());
    }

    @Test
    void askingForReliableDomainCoverageRefusesOverThem() throws Exception {
        Run compiled = compile(ON_THE_LINE_ONLY, "reliable-domain");

        assertEquals(1, compiled.code(), compiled.out() + compiled.err());
        assertTrue(compiled.err().contains("E1917"), compiled.err());
        assertTrue(compiled.err().contains("IN") || compiled.err().contains("OUT"), compiled.err());
    }

    /** The same measurement either way: what changes is which of its findings a build refuses. */
    @Test
    void theSameFindingIsReportedUnderTheOneBarAndRefusedUnderTheOther() throws Exception {
        assertFalse(compile(ON_THE_LINE_ONLY, "all").err().contains("E1917"),
                "the point is measured at `all` and not refused over");
    }

    @Test
    void aWordThatNamesNoBarIsRefusedWhereItIsWritten() throws Exception {
        Run compiled = compile(ON_THE_LINE_ONLY, "thorough");

        assertEquals(2, compiled.code(), compiled.out() + compiled.err());
        assertTrue(compiled.err().contains("off, witness, all or reliable-domain"), compiled.err());
    }

    /**
     * A criterion asks for evidence, and a verdict rests on the evidence it asks for.
     *
     * <p>The two halves of what a criterion means, held together. A build that refuses over a
     * missing {@code IN} row and calls a model satisfied while the {@code IN} point could not be
     * measured is held to one criterion where it refuses and another where it decides. The border
     * here is the pair: the points against the line came to an answer and the two away from it did
     * not.
     */
    @Test
    void aVerdictRestsOnTheEvidenceItsCriterionAsksFor() {
        PartitionEvidence measured = AReportOfOneBorder.partition(
                AReportOfOneBorder.measured(
                        AReportOfOneBorder.assessed(AReportOfOneBorder.aBoundedBorder(),
                                role -> role.againstTheLine()
                                        ? new ItemAssessment.Coverage.Hit()
                                        : new ItemAssessment.Coverage.Undecided())));

        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED,
                AReportOfOneBorder.verdictOf(measured, Adequacy.Criterion.SIMPLIFIED_DOMAIN),
                "the points it asks for came to an answer");
        assertEquals(AdequacyReport.AdequacyStatus.UNDETERMINED,
                AReportOfOneBorder.verdictOf(measured, Adequacy.Criterion.RELIABLE_DOMAIN),
                "two of the points it asks for did not");
    }

    private record Run(int code, String out, String err) {}

    private static Run compile(String model, String adequacy) throws Exception {
        Path file = Files.createTempDirectory("souther-reliable").resolve("limit.sou");
        Files.writeString(file, model);
        Path out = Files.createTempDirectory("souther-reliable-out");
        return cli("compile", file.toString(), "-d", out.toString(),
                "--adequacy", adequacy, "--warnings", "error");
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
