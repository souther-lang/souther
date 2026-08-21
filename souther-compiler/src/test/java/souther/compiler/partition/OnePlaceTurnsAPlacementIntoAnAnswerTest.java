package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeModel;
import java.lang.classfile.instruction.NewObjectInstruction;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.TreeSet;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A placement becomes an answer in one place, so that the last step cannot be written per shape.
 *
 * <p>What a search hands back is the same thing whatever it was searching for: one position at a
 * place of its carrier, two of them a distance apart, a form at a level. Each of those searches is
 * written on its own, and each also had to remember to hold what it found against the rules before
 * offering it — a placement inside every range can still be one the rules refuse, and offered as a
 * row it comes back refused where it is built, which a report says as every value having been
 * tried.
 *
 * <p>Two of the three did not remember. They were noticed one at a time, which is what a per-shape
 * obligation costs; the third would have been noticed the day a fourth shape of line was drawn. So
 * the obligation is not per shape: there is one place a placement becomes an answer, and a search
 * that goes round it fails here.
 *
 * <p>Read off the compiled classes, because what is checked is whose code runs the constructor and
 * no way of writing the call can dress that up as something else.
 */
class OnePlaceTurnsAPlacementIntoAnAnswerTest {

    private static final String FOUND = "souther.compiler.partition.Realization$Found";

    /** The one method that may make one. */
    private static final Set<String> MAY_MAKE_ONE =
            Set.of("souther.compiler.partition.LevelRealizer.found");

    @Test
    void nothingElseTurnsAPlacementIntoAnAnswer() throws IOException {
        Set<String> made = new TreeSet<>();
        for (Path each : classes()) {
            ClassModel model = ClassFile.of().parse(Files.readAllBytes(each));
            String from = model.thisClass().asInternalName().replace('/', '.');
            for (var method : model.methods()) {
                CodeModel code = method.code().orElse(null);
                if (code == null) {
                    continue;
                }
                for (var element : code) {
                    if (element instanceof NewObjectInstruction made0
                            && made0.className().asInternalName().replace('/', '.').equals(FOUND)) {
                        made.add(from + "." + method.methodName().stringValue());
                    }
                }
            }
        }
        assertFalse(made.isEmpty(),
                "nothing makes a placement into an answer at all; this check is reading no code");
        assertEquals(new TreeSet<>(MAY_MAKE_ONE), made,
                "who hands a placement back as an answer");
    }

    private static List<Path> classes() throws IOException {
        Path root = Path.of("target", "classes").toAbsolutePath();
        try (Stream<Path> walk = Files.walk(root)) {
            return walk.filter(each -> each.toString().endsWith(".class")).toList();
        }
    }
}
