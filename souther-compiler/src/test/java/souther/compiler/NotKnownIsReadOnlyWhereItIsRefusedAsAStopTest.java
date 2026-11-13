package souther.compiler;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where {@code GetsPast.NotKnown} is read, and what each reader does with it.
 *
 * <p>An operation nothing says the answer of is no operation a run gets past. A reader that took the
 * absence of a stop for a run getting past would credit a witness the program never reaches, so every
 * place that asks a completion whether it is {@code NotKnown} is written down with what it does:
 * the readers below treat it as an operation to refuse, never as one to pass. Every other reader asks
 * for the variant it can use ({@code Always}, {@code WhereTheTotalFits}, ...) and so is never handed
 * a {@code NotKnown} as an answer.
 *
 * <p>Compared whole: a new reader of it is a line to write down here with its reason.
 */
class NotKnownIsReadOnlyWhereItIsRefusedAsAStopTest {

    private static final Map<String, Integer> READERS = Map.of(
            // The cases of a completion in a switch over it: not known is not an answer on a run.
            "check/ContainerSizesUnderAWitness.java", 1,
            // Whether a completion is owed a proof: one not known to complete is owed none, so it
            // is left unsaid over what it reads, one that read no place is left unsaid on what no
            // place holds unless it is shown to stop none, and an obligation is refused it.
            "partition/Pullback.java", 1);

    @Test
    void theseAreTheOnlyPlacesThatAskWhetherACompletionIsNotKnown() throws IOException {
        Map<String, Integer> found = new TreeMap<>();
        for (Path source : sources()) {
            long reading = Files.readAllLines(source).stream()
                    .filter(line -> line.contains("GetsPast.NotKnown")
                            && !line.contains("new GetsPast.NotKnown()")
                            && !line.trim().startsWith("*") && !line.trim().startsWith("//"))
                    .count();
            if (reading > 0) {
                found.put(relative(source), (int) reading);
            }
        }
        assertEquals(new TreeMap<>(READERS), found,
                "a reader of NotKnown refuses it as a stop; one that took it for a run getting past"
                        + " would credit a witness the program does not reach");
    }

    private static String relative(Path source) {
        String path = source.toString().replace('\\', '/');
        return path.substring(path.indexOf("souther/compiler/") + "souther/compiler/".length());
    }

    private static List<Path> sources() throws IOException {
        Path main = Path.of("src/main/java/souther/compiler");
        assertTrue(Files.isDirectory(main), () -> "no " + main.toAbsolutePath());
        try (Stream<Path> walk = Files.walk(main)) {
            List<Path> found = new ArrayList<>(walk
                    .filter(each -> each.toString().endsWith(".java")).sorted().toList());
            assertTrue(found.size() > 100, () -> "that is not the compiler: " + found.size());
            return found;
        }
    }
}
