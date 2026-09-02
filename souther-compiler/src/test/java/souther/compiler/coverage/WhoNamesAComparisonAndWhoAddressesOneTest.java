package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Which comparison a reading is talking about, and where a run through one is written down, are
 * handed out by one place each.
 *
 * <p><b>Two names for two questions, and the answer to each has an owner.</b> Every comparison of
 * every body has a {@link ComparisonOccurrence}; what has a {@link ComparisonEmissionSite} is what
 * the plan instruments, which is fewer — a comparison behind an abort is one no run reaches. Held
 * as one value the two were the same number, so a reading asking which comparison it was looking at
 * got an answer that was true only while every comparison the catalog held had been numbered.
 *
 * <p>Which makes who may make one the thing to hold. A second place handing out occurrences is a
 * second naming, and two readers agreeing about which comparison they mean would come back down to
 * their having been given the same pair. A second place handing out addresses is a number the
 * emitter never wrote, and a claim about a run that no run can satisfy.
 *
 * <p>Read off the compiled classes, so what is counted is what a method does rather than what a
 * reading of the sources makes of it — a call written inside a lambda belongs to the lambda, and
 * this says so.
 *
 * <p>What this does not see is the tests, which are not in {@code target/classes}. A fixture that
 * writes a report about a comparison nothing compiled makes one of these by hand, and that is a
 * fixture standing in for a catalog rather than a second answer inside the compiler.
 */
class WhoNamesAComparisonAndWhoAddressesOneTest {

    private static final String OCCURRENCE = "souther/compiler/coverage/ComparisonOccurrence";

    private static final String SITE = "souther/compiler/coverage/ComparisonEmissionSite";

    /** A method that may make one, how many times it does, and why it is the one that does. */
    private record Licence(String who, int calls, String why) { }

    private static final List<Licence> MAY_NAME = List.of(
            new Licence("souther.compiler.coverage.ComparisonCatalog.of", 1,
                    "the one enumeration of what the bodies of a module hold, which is where a"
                            + " comparison first exists to be talked about"));

    private static final List<Licence> MAY_ADDRESS = List.of(
            new Licence("souther.compiler.coverage.CoverageSites.Plan.emissionSiteOf", 1,
                    "the plan's own numbering, read back for a comparison it instrumented"),
            new Licence("souther.compiler.coverage.Probe.compared", 1,
                    "what a probed class calls as it runs, which arrives as the number the emitter"
                            + " wrote into the call and has no catalog to ask anything of"));

    @Test
    void onlyTheCatalogNamesAComparisonOfABody() throws IOException {
        assertEquals(declared(MAY_NAME), callsToConstructor(OCCURRENCE),
                "a second place naming an occurrence is a second answer to which comparison a"
                        + " reading means. What may name one, and why: " + why(MAY_NAME));
    }

    @Test
    void onlyThePlanAndTheProbeAddressARun() throws IOException {
        assertEquals(declared(MAY_ADDRESS), callsToConstructor(SITE),
                "an address made anywhere else is a place no run was recorded at. What may make"
                        + " one, and why: " + why(MAY_ADDRESS));
    }

    private static Map<String, Integer> declared(List<Licence> licences) {
        Map<String, Integer> out = new TreeMap<>();
        licences.forEach(each -> out.put(each.who(), each.calls()));
        return out;
    }

    private static Map<String, String> why(List<Licence> licences) {
        Map<String, String> out = new LinkedHashMap<>();
        licences.forEach(each -> out.put(each.who(), each.why()));
        return out;
    }

    /** How many times each method of the compiler makes one of {@code owner}. */
    private static Map<String, Integer> callsToConstructor(String owner) throws IOException {
        Map<String, Integer> calls = new TreeMap<>();
        int read = 0;
        for (Path each : classes()) {
            ClassModel model = ClassFile.of().parse(Files.readAllBytes(each));
            read++;
            String from = model.thisClass().asInternalName().replace('/', '.').replace('$', '.');
            if (from.equals(owner.replace('/', '.'))) {
                // Its own constructor calling itself is not somebody making one.
                continue;
            }
            for (MethodModel method : model.methods()) {
                method.code().ifPresent(code -> code.forEach(element -> {
                    if (element instanceof InvokeInstruction call
                            && call.owner().asInternalName().equals(owner)
                            && call.name().stringValue().equals("<init>")) {
                        calls.merge(from + "." + method.methodName().stringValue(), 1, Integer::sum);
                    }
                }));
            }
        }
        assertFalse(read == 0, "no compiled class was read at all, so this says nothing");
        return calls;
    }

    private static List<Path> classes() throws IOException {
        Path root = Path.of("target", "classes").toAbsolutePath();
        try (Stream<Path> walk = Files.walk(root)) {
            return new ArrayList<>(walk.filter(p -> p.toString().endsWith(".class")).toList());
        }
    }
}
