package souther.cli;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.CodeModel;
import java.lang.classfile.instruction.NewObjectInstruction;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A measure's answer is chosen in one place, and nothing else builds one of its cases.
 *
 * <p>{@code PartitionDerivation.of} and {@code BoundaryDerivation.of} are the rule: what a measure
 * came to follows from what it found and whether its own reading ran out, and those two facts
 * arrive together or not at all. A caller writing {@code new Complete(entries)} decides it from the
 * entries alone, which is the reconstruction the type exists to stop — and is what every reader did
 * while the answer was a list beside a status.
 *
 * <p>The type cannot forbid it. {@code Absent} takes the proof that its own measure's reading ran
 * out, and that proof can only be made where the reading is; {@code Complete} claims the same thing
 * and carries entries instead, so a case public enough to match on is public enough to write. A
 * proof on {@code Complete} as well would close it, at the price of every fixture that wants a
 * measure made in full needing a reading to have made one — which is a price the tests that
 * fabricate a border to hold a criterion to cannot pay. So the rule is enforced here instead, and
 * this is the whole of what enforces it.
 *
 * <p><b>From the classes and not from the text.</b> Whether a constructor was invoked is not
 * something a search of source can answer: {@code import ...PartitionDerivation.Complete} and a bare
 * {@code new Complete(...)}, or a line break after {@code new}, are ordinary Java and read past any
 * pattern written for the qualified spelling. A {@code NEW} in the bytecode names the class it makes
 * however the source spelled it.
 *
 * <p><b>From every module that could hold one.</b> Which is why this is here: the classes of a
 * module are written when that module is built, so the same check in {@code souther-compiler} would
 * see one module's and call the rule kept. The modules it found are asserted below, so a run that
 * reaches fewer of them fails rather than passing over a smaller set.
 *
 * <p>Counted rather than allowed. Each site is one the introduction rule needs, so a helper added
 * beside {@code of} moves a number here — an exception this could not see would be one more case
 * built somewhere the rule never reached.
 */
class AMeasureIsIntroducedInOnePlaceTest {

    private static final String PARTITION = "souther.compiler.query.PartitionDerivation";
    private static final String BOUNDARY = "souther.compiler.query.BoundaryDerivation";

    /**
     * Every class that makes a case of a measure, and how many it makes.
     *
     * <p>The two interfaces are where {@code of} is compiled, and each makes its four: an absence,
     * a measure made in full, one made in part, and one whose reading did not run out.
     * {@code PartitionEvidence} makes the two {@code NoSubject}s of a {@code >->} composition,
     * which is the one case that claims nothing about a reading and so owes no proof.
     */
    private static final Map<String, Integer> SITES = new LinkedHashMap<>(Map.of(
            PARTITION, 4,
            BOUNDARY, 4,
            "souther.compiler.query.PartitionEvidence", 2));

    /** The modules whose classes can hold one, which is every module that reads a measure. */
    private static final List<String> MODULES =
            List.of("souther-build-driver", "souther-cli", "souther-compiler", "souther-lsp");

    @Test
    void nothingButTheIntroductionRuleBuildsACaseOfAMeasure()
            throws IOException, ClassNotFoundException {
        // The cases as the type says they are, so one added is one this counts without being told.
        List<String> cases = new ArrayList<>();
        for (String measure : List.of(PARTITION, BOUNDARY)) {
            for (Class<?> each : Class.forName(measure).getPermittedSubclasses()) {
                cases.add(each.getName());
            }
        }
        assertEquals(10, cases.size(), () -> "the cases of the two measures: " + cases);

        Path reactor = Path.of("").toAbsolutePath().getParent();
        List<String> seen = new ArrayList<>();
        Map<String, Integer> built = new LinkedHashMap<>();
        for (String module : MODULES) {
            Path classes = reactor.resolve(module).resolve("target/classes");
            if (!Files.isDirectory(classes)) {
                continue;
            }
            seen.add(module);
            try (Stream<Path> found = Files.walk(classes)) {
                for (Path each : found.filter(p -> p.toString().endsWith(".class")).toList()) {
                    countIn(Files.readAllBytes(each), cases, built);
                }
            }
        }

        assertEquals(MODULES, seen,
                "the modules this walked; a module whose classes are not there is one this says"
                        + " nothing about");
        assertEquals(SITES, built, "classes building a case of a measure rather than asking `of`");
    }

    /** The control the counts need: the cases are reachable from here at all. */
    @Test
    void andTheCasesAreClassesThisCanSee() throws ClassNotFoundException {
        assertTrue(Class.forName(PARTITION).isSealed(), PARTITION);
        assertTrue(Class.forName(BOUNDARY).isSealed(), BOUNDARY);
    }

    private static void countIn(byte[] bytes, List<String> cases, Map<String, Integer> built) {
        var model = ClassFile.of().parse(bytes);
        String owner = model.thisClass().asInternalName().replace('/', '.');
        model.methods().forEach(method ->
                method.code().ifPresent(code -> makesACase(code, owner, cases, built)));
    }

    private static void makesACase(CodeModel code, String owner, List<String> cases,
                                   Map<String, Integer> built) {
        code.forEach(element -> {
            if (element instanceof NewObjectInstruction made
                    && cases.contains(made.className().asInternalName().replace('/', '.'))) {
                // The owner and not the case. Which case is made is the introduction rule's
                // business; who makes one is this test's.
                built.merge(outermost(owner), 1, Integer::sum);
            }
        });
    }

    /** The class as it is written, since a case built inside a lambda is compiled into a method of
     *  the class that wrote it and the rule is about that class. */
    private static String outermost(String owner) {
        int nested = owner.indexOf('$');
        return nested < 0 ? owner : owner.substring(0, nested);
    }
}
