package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.jvm.ClassFileImage;

import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.constantpool.PoolEntry;
import java.lang.classfile.constantpool.Utf8Entry;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A class runs a pattern as the machine the compiler built, and names no regular-expression engine
 * (spec {@code [#a-pattern-runs-as-a-machine-a-class-holds]}).
 *
 * <p>Asked of the class files and not of the emitter's source, because what a class names is what
 * it can reach when it runs: a class naming {@code java.util.regex} anywhere — a field's type, a
 * call, a descriptor — is one that can hand text to a matcher with no bound on what it spends.
 * Every way a program states a pattern is here: a call in a body, a format a decoder holds a value
 * to, and the invariant a constructor checks.
 */
class NoGeneratedClassRunsAPatternThroughAnEngineTest {

    private static final String SOURCE = """
            module demo
            data Code = String invariant String.matches("[A-Z]{2}-[0-9]{4}", value)
            data In = { s: String }
            data Out = Bool
            behavior check : (i: In) -> Out constructs Out
            let check (i) = Out(String.matches("(a|b)*c", i.s))
            """;

    @Test
    void noClassNamesARegularExpressionEngine() {
        List<String> naming = new ArrayList<>();
        for (Map.Entry<String, ClassFileImage> each : Compiler.compile(SOURCE).entrySet()) {
            for (String said : utf8(each.getValue())) {
                if (said.contains("java/util/regex")) {
                    naming.add(each.getKey() + " names " + said);
                }
            }
        }
        assertEquals(List.of(), naming);
    }

    /**
     * Nor the library the machine is run by. A class loads its machine as a {@code Predicate} the
     * run time makes, so what it links against is the run time and the JDK. What it still takes
     * from the library is the image's format, which is {@code souther.runtime.Patterns}' to say.
     */
    @Test
    void noClassNamesTheLibraryThatRunsTheMachine() {
        List<String> naming = new ArrayList<>();
        for (Map.Entry<String, ClassFileImage> each : Compiler.compile(SOURCE).entrySet()) {
            for (String said : utf8(each.getValue())) {
                if (said.contains("net/unit8/notation199x")) {
                    naming.add(each.getKey() + " names " + said);
                }
            }
        }
        assertEquals(List.of(), naming);
    }

    /** And the classes that run a pattern name the run time's bootstrap for the machine, so an empty
     *  answer above means something. */
    @Test
    void theClassesThatRunAPatternNameTheMachine() {
        List<String> naming = new ArrayList<>();
        for (Map.Entry<String, ClassFileImage> each : Compiler.compile(SOURCE).entrySet()) {
            if (utf8(each.getValue()).stream()
                    .anyMatch(said -> said.contains("souther/runtime/Patterns"))) {
                naming.add(each.getKey());
            }
        }
        assertTrue(naming.containsAll(List.of("demo.Check$Impl", "demo.Code", "demo.Code$Dec")),
                "the behavior's call, the invariant's check and the decoder's format: " + naming);
    }

    private static List<String> utf8(ClassFileImage image) {
        ClassModel model = ClassFile.of().parse(image.bytes());
        List<String> out = new ArrayList<>();
        for (PoolEntry entry : model.constantPool()) {
            if (entry instanceof Utf8Entry text) {
                out.add(text.stringValue());
            }
        }
        return out;
    }
}
