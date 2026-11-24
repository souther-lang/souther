package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What is kept with the input outlives the Pullback that made it ({@code InputReading#derived}),
 * so it is the answer of a question that the key and the input settle, worked out by something
 * that is not a Pullback in the middle of its reading.
 *
 * <p>A Pullback in the middle of a reading holds what it has met and what it was told, and a
 * reading it makes leaves things in them. What a Pullback keeps for the rest of its own reading
 * is compared with that state and told again ({@code SharedReads}, {@code Pullback#kept}), and what
 * is kept with the input is not. So no Pullback asks for a memo of the input: the ones kept with
 * the input are asked by the readers that make a Pullback, or by what a Pullback is made for.
 */
class AReadingInTheMiddleOfAPullbackIsNotKeptWithTheInputTest {

    @Test
    void aPullbackKeepsNothingWithTheInput() throws IOException {
        List<String> found = Files.readAllLines(
                        Path.of("src/main/java/souther/compiler/partition/Pullback.java"))
                .stream()
                .filter(line -> !line.strip().startsWith("*") && !line.strip().startsWith("//")
                        && !line.strip().startsWith("/*"))
                .filter(line -> line.contains(".derived("))
                .map(String::strip)
                .toList();

        assertEquals(List.of(), found);
    }
}
