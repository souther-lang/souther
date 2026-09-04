package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Where a written value has a part is asked by the one walk that writes values.
 *
 * <p>{@code BehaviorInputs.stepWrittenValue} answers one of the two relations a path step stands
 * for: where a value written at a position has the part a step names. The other is what a value
 * standing there may be read as, and the two are one answer at a record and part at a sum whose
 * cases share a spread — a name every case spreads is readable at the sum and no row writes
 * anything at it.
 *
 * <p>So a reader that wants the second and takes this one reads no value at every name a model
 * reads through a sum. That is what the walk over a row's values did, and nothing said so: the
 * census in {@code NoQuestionAboutAShapeIsAnsweredOutOfAnothersAnswerTest} leaves out the class
 * that declares an answer and everything nested in it, which is right for the question it asks —
 * whether the answer left its owner — and blind to the two readers that live inside
 * {@link BehaviorInputs}. One of them wrote the defect.
 *
 * <p><b>So this counts methods and not classes.</b> The two callers were in one class file and a
 * class-level count cannot tell them apart. Read off what javac made rather than off the sources,
 * for the reason every check here is: a call is in the code however it was spelled.
 */
class OnlyTypeAtWrittenPathStepsIntoAWrittenValueTest {

    private static final String OWNER = "souther.compiler.partition.BehaviorInputs";

    private static final String ANSWERS = "stepWrittenValue";

    /**
     * The one method that reads a path as where a value goes.
     *
     * <p>With the descriptor, so that a second method of the name would be a second entry rather
     * than the same one seen twice.
     */
    private static final String COMPOSES =
            OWNER + "#typeAtWrittenPath(Lsouther/compiler/inputs/TermPath;)"
                    + "Lsouther/compiler/types/Type;";

    /**
     * And it is the only one, wherever it is written.
     *
     * <p>The walk that reads a row at a position takes its own steps ({@code BehaviorInputs
     * .Standing.step}) and appears here if it ever stops. What it would look like is this test
     * naming a second method — which is the reading of a row deciding where a value would be
     * written, one relation standing in for the other again.
     */
    @Test
    void oneMethodAsksWhereAWrittenValueHasItsParts() throws IOException {
        Set<String> asks = new TreeSet<>();
        for (Path each : classes()) {
            ClassModel model = ClassFile.of().parse(Files.readAllBytes(each));
            String from = model.thisClass().asInternalName().replace('/', '.');
            for (var method : model.methods()) {
                CodeModel code = method.code().orElse(null);
                if (code == null) {
                    continue;
                }
                for (var element : code) {
                    if (element instanceof InvokeInstruction call
                            && call.owner().asInternalName().replace('/', '.').equals(OWNER)
                            && call.name().stringValue().equals(ANSWERS)) {
                        asks.add(from + "#" + method.methodName().stringValue()
                                + method.methodType().stringValue());
                    }
                }
            }
        }

        assertFalse(asks.isEmpty(),
                "nothing asks where a written value has its parts at all; this check is reading no"
                        + " calls");
        assertEquals(Set.of(COMPOSES), asks,
                "a path is read as where a value goes in the one place that composes one, and a"
                        + " second reader is the written relation standing in for the read one");
    }

    /**
     * And there is one of it to ask, so the count above is the whole of the rule.
     *
     * <p>An overload beside it would be a second answer under one name: the count would go on
     * naming one caller while two questions were being answered, and which of them a caller meant
     * would be settled by the types it happened to hold.
     */
    @Test
    void thereIsOneAnswerUnderThatName() throws IOException {
        Set<String> declared = new TreeSet<>();
        ClassModel model = ClassFile.of().parse(Files.readAllBytes(fileOf(OWNER)));
        for (var method : model.methods()) {
            if (method.methodName().stringValue().equals(ANSWERS)) {
                declared.add(method.methodType().stringValue());
            }
        }

        assertEquals(Set.of("(Lsouther/compiler/inputs/TermPath$Step;Lsouther/compiler/types/Type;"
                        + "Lsouther/compiler/check/Symbols;)Lsouther/compiler/types/Type;"),
                declared,
                "where a written value has a part is one question, so it is answered by one method");
    }

    private static Path fileOf(String binaryName) {
        return root().resolve(binaryName.replace('.', '/') + ".class");
    }

    private static List<Path> classes() throws IOException {
        try (Stream<Path> walk = Files.walk(root())) {
            return new ArrayList<>(new LinkedHashSet<>(
                    walk.filter(each -> each.toString().endsWith(".class")).toList()));
        }
    }

    private static Path root() {
        return Path.of("target", "classes").toAbsolutePath();
    }
}
