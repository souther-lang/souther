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
 * Who may ask a statement for its parts ({@link Proposition#partsHeld}).
 *
 * <p>The parts are a list a reader recurses into, and a condition read through a name used twice
 * is held by two statements, so what a reader that recurses itself pays is every way down. The
 * ways down the parts for every other reader are {@link Proposition#anyPart},
 * {@link Proposition#everyPart}, {@link Proposition#eachPart}, {@link Proposition#sumOverParts},
 * {@link Proposition#overParts} and {@link Proposition#foldParts}, each handed a
 * {@link StatementReading} that asks each statement once. So the statement is the one that
 * goes down its own parts, and no list of readers allowed to is kept: what a reader outside it
 * does that is not asked of a statement once is {@link EveryReaderOfAStatementAsksEachStatementOnceTest}'s.
 */
class OnlyTheStatementGoesDownItsOwnPartsTest {

    private static final Pattern GOES_DOWN = Pattern.compile("\\.partsHeld\\(\\)");

    @Test
    void noReaderOutsideTheStatementAsksItForItsParts() throws IOException {
        Set<String> found = new TreeSet<>();
        Path main = Path.of("src/main/java/souther/compiler");
        try (Stream<Path> sources = Files.walk(main)) {
            for (Path source : (Iterable<Path>) sources
                    .filter(each -> each.toString().endsWith(".java"))::iterator) {
                String relative = main.relativize(source).toString().replace('\\', '/');
                if (!relative.equals("meaning/Proposition.java")
                        && GOES_DOWN.matcher(Files.readString(source)).find()) {
                    found.add(relative);
                }
            }
        }
        assertEquals(Set.of(), found);
    }
}
