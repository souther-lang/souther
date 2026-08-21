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
 * What stands directly under a type is worked out in one place.
 *
 * <p>The rule {@link AnInputIsReadInOnePlaceAndNoClaimNarrowsItTest} could not state. That one holds
 * a behavior's input to one reading by counting who calls {@link InputDomain#of}, and says in its own
 * javadoc what it cannot stop: a caller making a second reading out of the same declarations. The
 * generator was that caller. It never called {@code InputDomain.of} and never had to — it enumerated
 * a product's fields itself, three times, and the three were kept in step by hand and were already
 * out of step about how deep to go and about how a path is spelled.
 *
 * <p>So the line is drawn under the reading rather than around it: the step is
 * {@link StructuralDescent}'s, and whoever wants it takes it from there. A reader that wants
 * something else of a product — how far to follow it, where to stop, what type to follow it at — is
 * welcome to it, and gets no say in what is under a type.
 *
 * <p>A tripwire and not a proof. Somebody can put a helper in between, and the check would not see
 * it; what it does see is the line that has to be added first.
 */
class WhatIsUnderATypeIsDerivedInOnePlaceTest {

    /** Where a product's fields are taken off it. */
    private static final String THE_ONE_PLACE = "inputs/StructuralDescent.java";

    @Test
    void aProductsFieldsAreEnumeratedInOnePlace() throws IOException {
        List<Path> sources = mainSources();
        assertFalse(sources.isEmpty(), "found no sources at all — the scan missed the tree");
        assertTrue(sources.size() > 20,
                () -> "the scan found only " + sources.size() + " sources, which is not the tree");

        List<String> readers = new ArrayList<>();
        for (Path source : sources) {
            if (Files.readString(source, StandardCharsets.UTF_8).contains("product.fields()")) {
                readers.add(where(source));
            }
        }
        assertEquals(List.of(THE_ONE_PLACE), readers,
                "what is under a type is one fact; these work it out again");
    }

    /**
     * And the generator asks rather than knowing.
     *
     * <p>Named at the package rather than at the three methods that had a descent each: what the
     * rule forbids is the partitioning knowing a product when it sees one, and a fourth method
     * would be as much of a second answer as the three were.
     */
    @Test
    void nothingThatBuildsARowKnowsWhatAProductIs() throws IOException {
        List<String> naming = new ArrayList<>();
        for (Path source : mainSources()) {
            if (!source.getParent().getFileName().toString().equals("partition")) {
                continue;
            }
            if (Files.readString(source, StandardCharsets.UTF_8).contains("Shape.Product")) {
                naming.add(where(source));
            }
        }
        assertEquals(List.of(), naming,
                "where a value is built is not where it is settled what a value is made of");
    }

    private static String where(Path source) {
        return source.getParent().getFileName() + "/" + source.getFileName();
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
