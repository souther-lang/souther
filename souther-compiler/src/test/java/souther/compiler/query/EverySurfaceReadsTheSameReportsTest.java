package souther.compiler.query;

import souther.compiler.diag.EveryShippedMessageCatalogIsCompleteAndValidTest;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What the command line stops for and what an editor marks are the same problems, read once.
 *
 * <p>{@link Db#allReports()} is what the memo store collected, before anything asked where a reader
 * could be sent to any of it. A report about a module off the class path carries a coordinate in
 * text this compile reassembled: read from there, a run with one source quotes whatever sits at
 * those numbers in the file the author is looking at, and a run with several files it nowhere.
 * {@link Compilation#reports()} is that set read for where it may be said, and every surface reads
 * it — through {@code failure}, {@code errors}, {@code warnings} or {@code diagnostics}.
 *
 * <p>The two outputs were two readings, and the difference was invisible: a compile stopped on the
 * command line and left an editor showing a clean file with nothing generated. So the rule is that
 * there is one reading, and a surface added later does not get to pick.
 *
 * <p>A tripwire and not a proof. It reads the sources for the raw collection being asked for, and a
 * helper in between defeats it — the call that would have to be written first is the one this fails
 * on. Tests read the raw set freely: what they are usually about is the store itself, and a test
 * that wants what a reader is told asks for it the way a reader does.
 */
class EverySurfaceReadsTheSameReportsTest {

    /** Where the raw collection belongs: the store that answers it, and the one reading of it. */
    private static final Set<String> READS_IT = Set.of(
            "souther/compiler/query/Db.java",
            "souther/compiler/query/Compilation.java");

    @Test
    void nothingOutsideTheOneReadingCollectsTheRawReports() throws IOException {
        List<Path> sources = EveryShippedMessageCatalogIsCompleteAndValidTest.mainSources();
        assertFalse(sources.isEmpty(), "found no sources at all — the scan missed the tree");

        Set<String> reading = new TreeSet<>();
        for (Path source : sources) {
            String within = source.toString().replace('\\', '/').replaceAll(".*/src/main/java/", "");
            if (READS_IT.contains(within)) {
                continue;
            }
            // A call and not a mention: a reference in prose writes `Db#allReports()`, and saying
            // where the raw collection lives is what those references are for.
            if (Files.readString(source, StandardCharsets.UTF_8).contains(".allReports(")) {
                reading.add(within);
            }
        }
        assertEquals(Set.of(), reading,
                "the reports a reader is shown are the ones Compilation.reports() answers, read for"
                        + " where a reader can be sent to them; ask through failure, errors,"
                        + " warnings or diagnostics");
    }
}
