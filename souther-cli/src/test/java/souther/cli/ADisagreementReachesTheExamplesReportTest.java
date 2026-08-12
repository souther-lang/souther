package souther.cli;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

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

        ByteArrayOutputStream err = new ByteArrayOutputStream();
        PrintStream was = System.err;
        System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
        try {
            Main.main(new String[] {"examples", "--lang", "en", file.toString()});
        } finally {
            System.setErr(was);
        }
        String reported = err.toString(StandardCharsets.UTF_8);

        assertTrue(reported.contains("E1919"), reported);
        assertTrue(reported.contains("clash.sou:"), reported);
    }
}
