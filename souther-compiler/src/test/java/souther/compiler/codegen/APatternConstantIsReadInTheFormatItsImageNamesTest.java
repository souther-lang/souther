package souther.compiler.codegen;

import java.lang.invoke.MethodHandles;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Predicate;
import net.unit8.notation199x.pattern.PatternImage;
import net.unit8.notation199x.pattern.PatternMachine;
import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;
import org.junit.jupiter.api.Test;
import souther.runtime.Patterns;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The bootstrap a generated class loads its pattern through reads the image in the format the image
 * names, and refuses one in a format it does not read.
 *
 * <p>A class is compiled against one release of the text rules and may be run against another, so
 * what keeps it from being run as some other machine is that the image says its format and the
 * reader holds it to that: a release reads the formats earlier ones wrote, and refuses one it does
 * not read. What is asked here is that the run time's bootstrap goes through that reader rather
 * than around it: an image the compiler writes is read, and the same image with its format taken
 * off, or named as another, is refused where it is loaded.
 */
class APatternConstantIsReadInTheFormatItsImageNamesTest {

    @Test
    void anImageTheCompilerWritesIsReadAsItsPattern() {
        Predicate<String> run = loaded(written("[A-Z]{2}-[0-9]{4}"));
        assertTrue(run.test("AB-1234"));
        assertFalse(run.test("AB-123"));
    }

    @Test
    void anImageWithItsFormatTakenOffIsRefused() {
        List<String> image = written("[A-Z]{2}-[0-9]{4}");
        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> loaded(withFirst(image, afterTheFormat(image))));
        assertTrue(refused.getMessage().contains("format"), refused.getMessage());
    }

    @Test
    void anImageNamingAFormatTheReaderDoesNotReadIsRefused() {
        List<String> image = written("[A-Z]{2}-[0-9]{4}");
        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> loaded(withFirst(image, "NOT-A-FORMAT," + afterTheFormat(image))));
        assertTrue(refused.getMessage().contains("NOT-A-FORMAT"), refused.getMessage());
    }

    private static List<String> written(String pattern) {
        PatternRead.Read read = assertInstanceOf(PatternRead.Read.class, PatternParser.read(pattern));
        return assertInstanceOf(PatternImage.Written.class, PatternMachine.of(read.meaning()).image())
                .strings();
    }

    private static Predicate<String> loaded(List<String> image) {
        return Patterns.read(MethodHandles.lookup(), "pattern", Predicate.class,
                image.toArray(new String[0]));
    }

    /** The first string of {@code image} from just past the format it names, which an image ends
     *  with its first comma. */
    private static String afterTheFormat(List<String> image) {
        String first = image.getFirst();
        return first.substring(first.indexOf(',') + 1);
    }

    private static List<String> withFirst(List<String> image, String first) {
        List<String> out = new ArrayList<>(image);
        out.set(0, first);
        return out;
    }
}
