package souther.bench;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.instruction.NewObjectInstruction;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One method introduces a measure's answer, and nothing else makes a case of one.
 *
 * <p>{@code PartitionDerivation.of} and {@code BoundaryDerivation.of} are the rule: what a measure
 * came to follows from what it found and whether its own reading ran out, and those two facts
 * arrive together or not at all. A caller writing {@code new Complete(entries)} decides it from the
 * entries alone, which is the reconstruction the type exists to stop — and is what every reader did
 * while the answer was a list beside a status.
 *
 * <p>The type cannot forbid it. {@code Absent} takes the proof that its own measure's reading ran
 * out, and only the reading can make one; {@code Complete} claims the same thing and carries
 * entries instead, so a case public enough to match on is public enough to write. A proof on
 * {@code Complete} as well would close it, at the price of every fixture that wants a measure made
 * in full needing a reading to have made one — which the tests that fabricate a border to hold a
 * criterion to cannot pay. So this is the whole of what enforces the rule, and it is written to the
 * grain of the rule it enforces.
 *
 * <p><b>By the method and not by the class.</b> The rule names {@code of}. Counted per class, a
 * helper beside it that made a case would keep the class's total where it was and answer for
 * nothing — which is a check agreeing with a refactoring rather than with what was declared.
 *
 * <p><b>From the classes and not from the text.</b> Whether a constructor was invoked is not
 * something a search of source can answer: an {@code import ...PartitionDerivation.Complete} and a
 * bare {@code new Complete(...)}, or a line break after {@code new}, are ordinary Java and read
 * past any pattern written for the qualified spelling.
 *
 * <p><b>Over the modules the root pom names.</b> Which is why it is here: a module's classes exist
 * once that module is built, so the same check in the compiler would see one module's and call the
 * rule kept, and a check naming its own list of modules is a copy of the reactor that stops
 * covering the module added after it. Every module is a dependency of this one, which is what makes
 * {@code -am} build them and what makes this cover what it claims however the tree was built.
 */
class AMeasureIsIntroducedInOnePlaceTest {

    private static final String PARTITION = "souther.compiler.query.PartitionDerivation";
    private static final String BOUNDARY = "souther.compiler.query.BoundaryDerivation";

    /**
     * Every method that makes a case of a measure, and how many it makes.
     *
     * <p>{@code of} is the introduction rule and makes its four: an absence, a measure made in
     * full, one made in part, and one whose reading did not run out. {@code PartitionEvidence}
     * makes the two {@code NoSubject}s of a {@code >->} composition in its static initialiser,
     * which is the one case claiming nothing about a reading and so owing no proof.
     */
    private static final Map<String, Integer> INTRODUCED_BY = new LinkedHashMap<>(Map.of(
            PARTITION + "#of", 4,
            BOUNDARY + "#of", 4,
            "souther.compiler.query.PartitionEvidence#<clinit>", 2));

    @Test
    void nothingButTheIntroductionRuleMakesACaseOfAMeasure() throws Exception {
        List<String> cases = casesOf(PARTITION, BOUNDARY);

        assertEquals(10, cases.size(), () -> "the cases of the two measures: " + cases);

        Map<String, Integer> made = new LinkedHashMap<>();
        for (Path each : classes()) {
            ClassModel model = ClassFile.of().parse(Files.readAllBytes(each));
            String owner = outermost(model.thisClass().asInternalName().replace('/', '.'));
            model.methods().forEach(method -> method.code().ifPresent(code -> code.forEach(at -> {
                if (at instanceof NewObjectInstruction made_
                        && cases.contains(made_.className().asInternalName().replace('/', '.'))) {
                    made.merge(owner + "#" + method.methodName().stringValue(), 1, Integer::sum);
                }
            })));
        }
        assertEquals(INTRODUCED_BY, made,
                "what makes a case of a measure rather than asking `of`");
    }

    /**
     * The cases as the type says they are.
     *
     * <p>Asked of the sealed interface rather than listed, so a case added is one this counts
     * without being told — and a case renamed does not quietly leave the set.
     */
    private static List<String> casesOf(String... measures) throws ClassNotFoundException {
        List<String> out = new ArrayList<>();
        for (String measure : measures) {
            for (Class<?> each : Class.forName(measure).getPermittedSubclasses()) {
                out.add(each.getName());
            }
        }
        return out;
    }

    /** The class as it is written: a case made inside a lambda is compiled into a method of the
     *  class that wrote it, and the rule is about that class. */
    private static String outermost(String owner) {
        int nested = owner.indexOf('$');
        return nested < 0 ? owner : owner.substring(0, nested);
    }

    /**
     * Every compiled class of every module the reactor builds.
     *
     * <p>A module with nothing built is a hole and not a pass, which is what the assertion inside
     * says: a check that walks fewer modules than it claims answers about the ones it read and
     * says nothing about the rest.
     */
    private static List<Path> classes() throws IOException {
        List<Path> found = new ArrayList<>();
        for (String module : modules()) {
            Path root = repoRoot().resolve(module).resolve("target/classes");
            assertTrue(Files.isDirectory(root),
                    module + " has no built classes: this check covers what has been built, so a"
                            + " module that has not been is a hole rather than a pass");
            try (Stream<Path> walk = Files.walk(root)) {
                walk.filter(each -> each.toString().endsWith(".class")).forEach(found::add);
            }
        }
        return found;
    }

    /** The modules the root pom names, which is what the reactor builds. */
    private static List<String> modules() {
        String pom;
        try {
            pom = Files.readString(repoRoot().resolve("pom.xml"));
        } catch (IOException unreadable) {
            throw new UncheckedIOException(unreadable);
        }
        List<String> out = new ArrayList<>();
        Matcher named = Pattern.compile("<module>([^<]+)</module>").matcher(pom);
        while (named.find()) {
            out.add(named.group(1));
        }
        assertTrue(out.size() > 1, () -> "the root pom names " + out);
        return out;
    }

    private static Path repoRoot() {
        return Path.of("").toAbsolutePath().getParent();
    }
}
