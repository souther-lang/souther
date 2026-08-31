package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.test.RepositoryLayout;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a row is written for is put together in one place, and nowhere else in the compiler.
 *
 * <p>A subject is a reading of an input and the axes a measurement of that input came to. Nothing
 * about either value says they are of one measurement: an axis carries the classes and the lines a
 * body drew, which the reading does not determine, and two behaviors taking a parameter spelled the
 * same way have a root apiece — so a caller holding both can pair a reading with axes measured
 * somewhere else and every check either value can make will pass. A row would then be composed on
 * one measurement's orders and read back through the other's walk.
 *
 * <p>What can be held to instead is where the pair is made. One place asks the same
 * {@code (module, behavior)} for the geometry and for the reading of the input, and makes the
 * subject there; every other reader takes the subject whole. So this counts the places, and a second
 * one is a failure here rather than a defect somebody meets later.
 *
 * <p><b>Counted in the sources rather than declared in a list.</b> A list of allowed callers is a
 * thing to keep up to date, and the first person to add one keeps it up to date by adding
 * themselves. The count is what the rule says.
 */
class OneMeasurementIsPairedWithOneReadingInOnePlaceTest {

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    /** Where a subject is made: the factory that takes a reading and the axes measured at it. */
    private static final String MINTED = "MeasuredInput.of(";

    @Test
    void oneProductionPlaceMakesASubject() throws IOException {
        List<Path> sources = REPOSITORY.mainJavaSources();
        assertTrue(sources.size() > 20,
                () -> "the scan found only " + sources.size() + " sources, which is not the tree");

        List<String> makes = new ArrayList<>();
        for (Path source : sources) {
            String text = code(Files.readString(source, StandardCharsets.UTF_8));
            if (text.contains(MINTED)) {
                makes.add(source.getParent().getFileName() + "/" + source.getFileName());
            }
        }

        assertEquals(List.of("query/Adequacy.java"), makes,
                "the reading and the axes measured at it are paired in one place, and a second"
                        + " place is a caller choosing which reading a measurement is of");
    }

    /** {@code source} with its comments taken out, which is what this reads: a file may say what
     *  the rule is without being a place that makes one. */
    private static String code(String source) {
        return source.replaceAll("(?s)/\\*.*?\\*/", " ").replaceAll("//[^\n]*", " ");
    }
}
