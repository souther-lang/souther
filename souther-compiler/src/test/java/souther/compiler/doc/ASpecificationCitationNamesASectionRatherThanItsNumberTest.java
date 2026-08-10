package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.charset.MalformedInputException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the repository writes when it points at the specification, held against what the reader's own
 * lookup answers.
 *
 * <p>Two rules, because a citation can be wrong in two ways that no single check catches. One is
 * that the name does not resolve — a section renamed or removed leaves every citation of it pointing
 * nowhere, and only asking the resolver finds that. The other is that the citation is written as a
 * section number. A number is not a name the document gives a section: it is produced from the
 * heading's position by {@code :sectnums:}, so inserting a heading re-issues every number after it
 * and nothing in the text changes. Between 2026-08-01 and the day this was written, 171 of 172
 * anchors survived unchanged while only 13 of them kept their number.
 *
 * <p>So the first rule alone would pass a tree full of numbers — they are not names, so they are not
 * names that fail to resolve — and the second alone would pass a citation naming a section that was
 * deleted.
 */
class ASpecificationCitationNamesASectionRatherThanItsNumberTest {

    /**
     * A citation: {@code §} and the name of a section. The name opens with a letter, which is what
     * separates a citation of this document from a reference into another one — {@code §8.5.5} in an
     * ADR is a chapter of the smdd-book and names nothing here.
     */
    private static final Pattern CITATION = Pattern.compile("§([a-zA-Z][a-zA-Z0-9_-]*)");

    /**
     * A section number written where a citation goes — {@code spec <number>}, with or without the
     * word {@code section} between them, and whether the number names a chapter or a subsection.
     */
    private static final Pattern BY_NUMBER = Pattern.compile(
            "\\b[Ss]pec(?:ification)?s?\\s+(?:sections?\\s+)?[0-9]+(?:\\.[0-9]+)*");

    /**
     * The files that say why a section number is not a citation, and so have to write one, with how
     * many each writes. Counted rather than merely allowed: a file that may quote the mistake is not
     * a file that may make it, and the number is what tells the two apart.
     *
     * <p>Neither the number quoted nor this rule's own examples are written out here. They would be
     * occurrences themselves, and a rule that has to exempt itself no longer holds over its own text.
     */
    private static final Map<String, Integer> SAYS_WHY_NOT_TO = Map.of(
            "docs/adr/0101-a-diagnostic-says-the-values-it-carries.md", 1,
            "souther-compiler/src/test/java/souther/compiler/diag/"
                    + "EveryShippedMessageCatalogIsCompleteAndValidTest.java", 1);

    @Test
    void everyCitationNamesASectionAReaderCanRead() {
        SpecDocument spec = SpecDocument.bundled();
        List<String> dangling = new ArrayList<>();
        for (Map.Entry<String, String> file : sources().entrySet()) {
            Matcher cited = CITATION.matcher(file.getValue());
            while (cited.find()) {
                if (spec.section(cited.group(1)) == null) {
                    dangling.add(file.getKey() + " cites `" + cited.group(1) + "`");
                }
            }
        }

        assertEquals(List.of(), new ArrayList<>(new TreeSet<>(dangling)),
                "a citation sends a reader to a section that is not there");
    }

    @Test
    void theOnlySectionNumbersLeftAreTheOnesSayingWhyNotToWriteOne() {
        SortedMap<String, Integer> written = new TreeMap<>();
        for (Map.Entry<String, String> file : sources().entrySet()) {
            Matcher cited = BY_NUMBER.matcher(file.getValue());
            while (cited.find()) {
                written.merge(file.getKey(), 1, Integer::sum);
            }
        }

        // Equality rather than containment, in both directions at once: a number written anywhere
        // else is a citation nothing resolves, and a second one in a file allowed to quote the
        // mistake is a file making it.
        assertEquals(new TreeMap<>(SAYS_WHY_NOT_TO), written,
                "a section number is a position rather than a name; cite the anchor by its name");
    }

    /**
     * A citation is found at all, so neither rule above is passing over an empty scan. Held against a
     * count rather than emptiness because a walk that reached one file would also be non-empty.
     */
    @Test
    void theWalkReachesTheCitationsThereAreToCheck() {
        int found = 0;
        for (String text : sources().values()) {
            Matcher cited = CITATION.matcher(text);
            while (cited.find()) {
                found++;
            }
        }

        assertTrue(found > 400, "the walk found only " + found + " citations — it missed the tree");
    }

    /** Every text file in the repository, keyed by its path from the root. */
    private static Map<String, String> sources() {
        Path repo = repositoryRoot();
        Map<String, String> files = new LinkedHashMap<>();
        try (Stream<Path> walk = Files.walk(repo)) {
            for (Path path : walk.filter(Files::isRegularFile).filter(p -> !isBuildOutput(repo, p)).toList()) {
                try {
                    files.put(repo.relativize(path).toString().replace('\\', '/'),
                            Files.readString(path));
                } catch (MalformedInputException notText) {
                    // A jar or an image says nothing about the specification.
                }
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        return files;
    }

    /** Whether {@code path} is generated or git's own, neither of which anyone writes a citation in. */
    private static boolean isBuildOutput(Path repo, Path path) {
        for (Path part : repo.relativize(path)) {
            String name = part.toString();
            if (name.equals("target") || name.equals(".git")) {
                return true;
            }
        }
        return false;
    }

    /** The repository root. A test runs in its own module's directory, whose parent that is. */
    private static Path repositoryRoot() {
        Path module = Path.of("").toAbsolutePath();
        return Files.isDirectory(module.resolve(Path.of("src", "main", "java")))
                ? module.getParent() : module;
    }
}
