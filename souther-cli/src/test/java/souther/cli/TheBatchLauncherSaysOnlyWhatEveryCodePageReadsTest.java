package souther.cli;

import org.junit.jupiter.api.Test;
import souther.test.RepositoryLayout;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * cmd.exe reads a batch file in whatever code page the console it runs in is set to, and the file
 * carries no declaration of its own. A character written outside what every such code page agrees
 * on is read as whatever the bytes mean there: in a message it reaches the user as the wrong
 * characters, and it is the reader whose console differs from the author's who sees it.
 *
 * <p>So the launcher says only what they agree on. The rule is on the whole file rather than on the
 * lines that speak, because what a prose line explains today is what a message quotes tomorrow, and
 * a rule that stopped at the messages would be a rule the next edit steps over without noticing.
 */
class TheBatchLauncherSaysOnlyWhatEveryCodePageReadsTest {

    @Test
    void theLauncherIsWrittenInTheCharactersEveryCodePageAgreesOn() throws Exception {
        Path launcher = RepositoryLayout.ofWorkingDirectory().root()
                .resolve("souther-cli/src/main/launcher/souther.cmd");
        assertTrue(Files.isRegularFile(launcher), launcher + " is where the batch launcher is");

        byte[] written = Files.readAllBytes(launcher);
        List<String> outside = new ArrayList<>();
        int line = 1;
        for (byte each : written) {
            if (each == '\n') {
                line++;
            } else if ((each & 0xFF) > 0x7F) {
                outside.add("line " + line + " holds " + String.format("0x%02X", each & 0xFF));
            }
        }
        assertTrue(outside.isEmpty(), () -> launcher.getFileName() + " is read in whichever code page"
                + " the console has, and holds bytes they do not agree on: " + outside);
    }
}
