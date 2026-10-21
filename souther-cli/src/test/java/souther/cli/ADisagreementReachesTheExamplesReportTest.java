package souther.cli;

import souther.cli.CliProcess.Ran;
import org.junit.jupiter.api.Test;

import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An {@code example} and a {@code fake} that disagree are told to whoever ran the command.
 *
 * <p>That they disagree at all, and how many times it is said, are the compiler's questions and are
 * asked of it ({@code CompileFakeExampleDisagreementTest}). What is asked here is the last step: the
 * report {@code souther examples} writes carries the code and the file the disagreement stands in,
 * so a reader who ran the command finds it without being told where else to look.
 */
class ADisagreementReachesTheExamplesReportTest {

    private static final String CLASHING = """
            module example.clash

            data MemberId = String
            data Found = { id: MemberId }
            data Missing = { why: String }

            behavior findMember : (id: MemberId) -> Found | Missing

            example findMember
                | "m-1 is a member" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }

            fake findMember
                | (MemberId("m-1")) -> Missing { why = "no such member" }
            """;

    @Test
    void theDisagreementReachesTheExamplesReport() throws Exception {
        Path file = Files.createTempDirectory("souther-disagree").resolve("clash.sou");
        Files.writeString(file, CLASHING);

        Ran ran = CliInProcess.run("examples", "--lang", "en", file.toString());
        String reported = ran.err();

        assertEquals(0, ran.code(), "a disagreement is reported, and the run still answers: "
                + reported);
        assertTrue(reported.contains("E1919"), reported);
        assertTrue(reported.contains("clash.sou:"), reported);
    }
}
