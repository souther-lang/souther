package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Who makes a {@link LevelRealizer}, because what it has proved is held for as long as it is.
 *
 * <p>The class check of a point and the search of the same point read one proof only when they are
 * asked of one realizer, and a realizer made at either of them would prove it a second time with
 * nothing to tell the two apart: the answers are the same, and so is every test of them. So the
 * places a realizer is made are held to a list, and a place added to it has to say whose proofs it
 * is.
 *
 * <p>The list is compared whole rather than counted, for the reason a count is not enough: one site
 * can be dropped and another added without the number moving.
 */
class TheRealizerOfASearchIsMadeWhereItsProofsHaveAnOwnerTest {

    private static final String MAKES = "new LevelRealizer(";

    /**
     * The files that make one and how many times each does.
     *
     * <p>{@code query/Coverages.java} twice: once for each border a search looks along, handed to
     * the class check and to the search of that border alike, and once for the measuring of one
     * point, which builds the region it asks about in the same breath and has no second asking to
     * share a proof with. {@code query/Adequacy.java} once, which asks one question and drops the
     * realizer.
     */
    private static final Map<String, Integer> MAKERS = Map.of(
            "query/Coverages.java", 2,
            "query/Adequacy.java", 1);

    @Test
    void theseAreTheOnlyPlacesOneIsMade() throws IOException {
        Map<String, Integer> made = new TreeMap<>();
        for (Path source : sources()) {
            String text = Files.readString(source);
            int at = 0;
            int count = 0;
            while ((at = text.indexOf(MAKES, at)) >= 0) {
                count++;
                at += MAKES.length();
            }
            if (count > 0) {
                made.put(relative(source), count);
            }
        }
        assertEquals(new TreeMap<>(MAKERS), made,
                "a realizer made where a proof is asked for is one that proves it again; make it where"
                        + " the search it serves begins, and add the place here with whose it is");
    }

    /**
     * And a search makes its realizer for the border and not before the borders.
     *
     * <p>One made ahead of them would hold the regions of every border to the last, and none of
     * them is asked about by another: each is made for the border it is searched in.
     */
    @Test
    void aSearchMakesItsRealizerInsideTheLoopOverItsBorders() throws IOException {
        String text = Files.readString(
                Path.of("src/main/java/souther/compiler/query/Coverages.java"));
        int start = text.indexOf("static LineReadings searched(");
        int loop = text.indexOf("for (BorderAssessment border : measured.each())", start);
        assertTrue(start >= 0 && loop > start, "the search of the borders has moved");
        assertFalse(text.substring(start, loop).contains(MAKES),
                "a realizer made before the loop over the borders outlives each of them");
        int body = text.indexOf("return new LineReadings(out, measured.tilts());", loop);
        assertTrue(text.substring(loop, body).contains(MAKES),
                "the loop over the borders makes the realizer its border is searched with");
    }

    private static String relative(Path source) {
        String path = source.toString().replace('\\', '/');
        return path.substring(path.indexOf("souther/compiler/") + "souther/compiler/".length());
    }

    private static List<Path> sources() throws IOException {
        Path main = Path.of("src/main/java/souther/compiler");
        assertTrue(Files.isDirectory(main), () -> "no " + main.toAbsolutePath());
        try (Stream<Path> walk = Files.walk(main)) {
            List<Path> found = walk.filter(each -> each.toString().endsWith(".java"))
                    .sorted().toList();
            assertTrue(found.size() > 100, () -> "that is not the compiler: " + found.size());
            return found;
        }
    }
}
