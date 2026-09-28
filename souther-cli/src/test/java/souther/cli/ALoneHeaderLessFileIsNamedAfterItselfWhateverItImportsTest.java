package souther.cli;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A lone file with no {@code module} header is named after the file, and a class path does not
 * change that.
 *
 * <p>The class path says which modules an import may reach, and the header says what the file is
 * called. Handed a file and a class path, {@code compile} takes both as given: the file still takes
 * its stem, and an import in it resolves against the path.
 */
class ALoneHeaderLessFileIsNamedAfterItselfWhateverItImportsTest {

    @TempDir
    Path dir;

    @Test
    void aLoneHeaderLessFileImportsOffTheClassPathUnderItsOwnName() throws Exception {
        Path lib = dir.resolve("money.sou");
        Files.writeString(lib, """
                module shared.money exposing ( Amount )
                data Amount = Int
                    invariant value >= 0
                """);
        Path libClasses = dir.resolve("lib-classes");
        Main.compileToDir(List.of(lib), libClasses);

        Path app = dir.resolve("orders.sou");
        Files.writeString(app, """
                import shared.money ( Amount )
                data Order = { total: Amount }
                """);
        Path appClasses = dir.resolve("app-classes");
        Main.compileToDir(List.of(app), appClasses, List.of(libClasses));

        assertTrue(Files.exists(appClasses.resolve("orders/Order.class")),
                "named after its file, whatever it imports");
    }
}
