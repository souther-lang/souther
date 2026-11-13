package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Who may go down the parts of a statement ({@link Proposition#partsHeld}).
 *
 * <p>A condition read through a name used twice is held by two statements, so the statements are a
 * graph, and the ways down a chain of names each using the one before it twice are two to the
 * depth. What a reader wants of a statement that is the same wherever it stands — whether some part
 * answers only where an operation does, why the first part nothing read stopped — is the
 * statement's to say once ({@link SharedPropositions#fact}), and a reader that goes down the parts
 * for it pays for every way. A reader that goes down them because what it works out differs by
 * where a part stands is one of these listed, and keeps what it learns of a part for the walk it
 * is in.
 *
 * <p>A reader not listed asks a statement, or is added to {@link SharedPropositions.Fact} and the
 * list stays as it is.
 */
class OnlyTheReadersListedGoDownThePartsOfAStatementTest {

    private static final Pattern GOES_DOWN = Pattern.compile("\\bpartsHeld\\(\\)");

    private static final Set<String> LISTED = Set.of(
            "meaning/Conclusion.java",
            "meaning/Derivation.java",
            "meaning/PositionsAStatementReads.java",
            "meaning/Proposition.java",
            "meaning/Quantity.java",
            "meaning/TruthTable.java",
            "meaning/WhereEachLineDecides.java",
            "meaning/WrittenLines.java",
            "meaning/WrittenOfANode.java",
            "partition/AStatementAtARow.java",
            "partition/Cutting.java",
            "partition/KeyOrderCandidates.java",
            "partition/Pullback.java");

    @Test
    void noReaderOutsideTheListGoesDownThePartsOfAStatement() throws IOException {
        Set<String> found = new TreeSet<>();
        Path main = Path.of("src/main/java/souther/compiler");
        try (Stream<Path> sources = Files.walk(main)) {
            for (Path source : (Iterable<Path>) sources
                    .filter(each -> each.toString().endsWith(".java"))::iterator) {
                if (GOES_DOWN.matcher(Files.readString(source)).find()) {
                    found.add(main.relativize(source).toString().replace('\\', '/'));
                }
            }
        }
        assertEquals(new TreeSet<>(LISTED), found);
    }
}
