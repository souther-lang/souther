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
import static org.junit.jupiter.api.Assertions.assertFalse;
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
     *
     * <p>The section sign is allowed for and refused rather than left out. Now that a citation is
     * spelled {@code §} and a name, writing {@code §} and the old number is the likeliest way to
     * write a number, and it is the one form neither rule would otherwise see: it is not a name, so
     * nothing fails to resolve, and it is not a bare number either.
     */
    private static final Pattern BY_NUMBER = Pattern.compile(
            "\\b[Ss]pec(?:ification)?s?\\s+(?:sections?\\s+)?§?[0-9]+(?:\\.[0-9]+)*");

    /**
     * A citation with the word {@code spec} left off — a bare number in parentheses, carrying on
     * from a full citation earlier in the same comment. Nineteen of them survived the sweep that
     * only looked for the word, four in one Javadoc paragraph.
     *
     * <p>Asked of comment lines in Java and Souther sources alone. There a parenthesised number
     * that carries a dot is a section and nothing else — the sweep that found these turned up no
     * other kind. Prose elsewhere writes a version and a decimal the same way.
     */
    private static final Pattern ELIDED = Pattern.compile(
            "\\((\\d+\\.\\d+(?:\\s*,\\s*\\d+(?:\\.\\d+)?)*)\\)");

    /** Where a comment starts, in the two source languages the elided form was written in. */
    private static final Pattern COMMENT = Pattern.compile("^\\s*(\\*|//|/\\*)");

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
            String path = file.getKey();
            Matcher cited = BY_NUMBER.matcher(file.getValue());
            while (cited.find()) {
                written.merge(path, 1, Integer::sum);
            }
            if (!elidable(path)) {
                continue;
            }
            for (String line : file.getValue().split("\n", -1)) {
                Matcher elided = COMMENT.matcher(line).find()
                        ? ELIDED.matcher(line) : ELIDED.matcher("");
                while (elided.find()) {
                    written.merge(path, 1, Integer::sum);
                }
            }
        }

        // Equality rather than containment, in both directions at once: a number written anywhere
        // else is a citation nothing resolves, and a second one in a file allowed to quote the
        // mistake is a file making it.
        assertEquals(new TreeMap<>(SAYS_WHY_NOT_TO), written,
                "a section number is a position rather than a name; cite the anchor by its name");
    }

    /**
     * Both shapes the rule refuses, held against the rule itself rather than against the tree. The
     * tree passing says nothing about what the rule would catch, and the shape worth pinning is the
     * one that reads as a citation: the section sign with the old number behind it.
     *
     * <p>The word and the number are joined here rather than written together, so this file holds
     * neither shape and the rule holds over it like any other.
     */
    @Test
    void aNumberIsRefusedWhetherOrNotItIsWrittenAsIfItWereAName() {
        String word = "spec";

        assertTrue(BY_NUMBER.matcher(word + " 13.1").find(), "a number on its own");
        assertTrue(BY_NUMBER.matcher(word + " §13.1").find(), "a number spelled as if it were a name");
        assertTrue(BY_NUMBER.matcher(word + " section 20").find(), "a chapter, said in words");
        assertTrue(ELIDED.matcher("carried on from the citation above (13.1)").find(),
                "a second reference with the word left off");

        assertFalse(BY_NUMBER.matcher(word + " §fn-declaration").find(), "a name is not a number");
        assertFalse(ELIDED.matcher("runs in O(1) amortized").find(), "nor is a complexity");
        assertFalse(ELIDED.matcher("builds Amount(500)").find(), "nor an argument");
    }

    /** Whether {@code path} is a source whose comments are read for the elided form. */
    private static boolean elidable(String path) {
        return path.endsWith(".java") || path.endsWith(".sou");
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

    /**
     * Every text file in the repository, keyed by its path from the root, read once for the class.
     *
     * <p>Every text file the repository holds outside {@code target} and {@code .git}, which is
     * what a citation could be written in. Nobody writes one while the class runs, and each of the
     * four checks below was reading all of it again to ask its own question of the same text.
     */
    private static Map<String, String> read;

    private static Map<String, String> sources() {
        if (read == null) {
            read = walk();
        }
        return read;
    }

    /** The walk itself, taken the once. */
    private static Map<String, String> walk() {
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
