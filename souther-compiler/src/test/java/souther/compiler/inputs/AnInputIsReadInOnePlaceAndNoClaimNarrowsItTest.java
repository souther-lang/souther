package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What can arrive at an input is read once, and nothing a body says narrows it.
 *
 * <p>Two rules the types cannot hold on their own. A {@link Position} cannot be written down — the
 * interface is sealed over a package-private record — so no caller can assemble a reading; what
 * nothing stops is a caller <em>making a second one</em> from the same declarations. It would agree
 * with the first until the day the trees they are given stop being the same tree, and the disagreement
 * would show up as a case one measure asks for a row at and another does not.
 *
 * <p>The second rule is the whole of what issue #778 was about. A claim a body makes is judged
 * against this reading and reported; it never reaches the reading, and it never reaches the
 * partition drawn from it. Written as a sentence in a javadoc, that is a rule somebody has to
 * remember at each place a denominator is counted.
 *
 * <p>Both are asked of the sources. These are tripwires and not proofs — a helper in between defeats
 * either — but the line that would have to be added first is the one this fails on.
 */
class AnInputIsReadInOnePlaceAndNoClaimNarrowsItTest {

    /** Where a behavior's input is read: the query that owns the answer and hands it to every
     *  measure, to the generator, and to the check that refuses a claim the rules contradict. */
    private static final String THE_ONE_PLACE = "query/Adequacy.java";

    /** The packages a denominator is counted in. What is owed at a position and which classes it
     *  divides into are decided here, and a claim reaching either is a claim moving a measure. */
    private static final List<String> WHERE_DENOMINATORS_ARE = List.of("inputs", "partition");

    /**
     * And the files that count one inside a package that also reports.
     *
     * <p>{@code query} holds both halves — the measures and what a report says about them — so the
     * package alone is too coarse a line. These two count: {@code Adequacy} the cases a signature is
     * owed, {@code Coverages} the classes a position is owed. What a body claimed is put beside
     * their answers afterwards, by a file that counts nothing.
     */
    private static final List<String> WHAT_COUNTS_ONE =
            List.of("query/Adequacy.java", "query/Coverages.java");

    @Test
    void everyReadingOfAnInputComesFromTheOneQueryThatMakesThem() throws IOException {
        List<Path> sources = mainSources();
        assertFalse(sources.isEmpty(), "found no sources at all — the scan missed the tree");

        List<String> callers = new ArrayList<>();
        for (Path source : sources) {
            String text = Files.readString(source, StandardCharsets.UTF_8);
            // The declaration itself, and prose naming it, are not calls.
            if (source.endsWith(Path.of("inputs", "InputDomain.java"))
                    || !text.contains("InputDomain.of(")) {
                continue;
            }
            callers.add(source.getParent().getFileName() + "/" + source.getFileName());
        }
        assertEquals(List.of(THE_ONE_PLACE), callers,
                "an input is read in one place; these read it again");
    }

    @Test
    void nothingThatCountsADenominatorNamesAClaim() throws IOException {
        List<Path> sources = mainSources();
        List<String> reading = new ArrayList<>();
        List<String> naming = new ArrayList<>();
        for (Path source : sources) {
            String where = source.getParent().getFileName() + "/" + source.getFileName();
            if (!WHERE_DENOMINATORS_ARE.contains(source.getParent().getFileName().toString())
                    && !WHAT_COUNTS_ONE.contains(where)) {
                continue;
            }
            reading.add(where);
            if (Files.readString(source, StandardCharsets.UTF_8).contains("souther.compiler.claims")) {
                naming.add(where);
            }
        }
        assertTrue(reading.size() > 20, () -> "the scan found only " + reading.size()
                + " sources where a denominator is counted, which is not the tree");
        assertTrue(reading.containsAll(WHAT_COUNTS_ONE),
                () -> "the two files that count a denominator beside a report were not scanned: "
                        + reading);
        assertEquals(List.of(), naming,
                "a claim cannot narrow what a row is owed, and these can reach one");
    }

    /** And the claims are named somewhere, so that the row above is a rule rather than a search for
     *  a package nothing uses. */
    @Test
    void theClaimsAreReadWhereTheyAreJudgedAndReported() throws IOException {
        List<String> readers = new ArrayList<>();
        for (Path source : mainSources()) {
            if (Files.readString(source, StandardCharsets.UTF_8).contains("souther.compiler.claims")
                    && !source.getParent().getFileName().toString().equals("claims")) {
                readers.add(source.getParent().getFileName() + "/" + source.getFileName());
            }
        }
        assertEquals(List.of("query/Bodies.java", "query/ClaimAnnotations.java"),
                readers.stream().sorted().toList(),
                "a claim is judged where the bodies are checked and turned into words for a report,"
                        + " and nothing else sees one");
    }

    private static List<Path> mainSources() throws IOException {
        Path module = Path.of("").toAbsolutePath();
        Path repo = Files.isDirectory(module.resolve(Path.of("src", "main", "java")))
                ? module.getParent() : module;
        List<Path> sources = new ArrayList<>();
        try (Stream<Path> modules = Files.list(repo)) {
            for (Path candidate : modules.toList()) {
                Path root = candidate.resolve(Path.of("src", "main", "java"));
                if (!Files.isDirectory(root)) {
                    continue;
                }
                try (Stream<Path> walk = Files.walk(root)) {
                    walk.filter(p -> p.toString().endsWith(".java")).forEach(sources::add);
                }
            }
        }
        sources.sort(Path::compareTo);
        return sources;
    }
}
