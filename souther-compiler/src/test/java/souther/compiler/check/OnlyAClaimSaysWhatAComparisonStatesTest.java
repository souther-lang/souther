package souther.compiler.check;

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
import java.util.Set;
import java.util.TreeMap;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Who puts a canonical comparison together, and who asks for one.
 *
 * <p>Two questions, and they break differently. What a comparison of two values states is derived
 * from the two facts a claim holds, and that derivation is the claim's: a second one is a table of
 * six that agrees with this one only for as long as somebody keeps it so. Who may ask a claim for
 * the answer is a different matter — a reader that has to write a comparison down asks, and one
 * more of them is one more consumer and not one more derivation.
 *
 * <p><b>What the visibility does not do.</b> {@link CanonicalComparison} is this package's, which
 * keeps it out of the vocabulary anything outside reads. It does not decide who calls what: a
 * method whose answer nothing outside can name is still a method anything can call, so both
 * questions are answered here rather than by the language.
 *
 * <p>Read off the compiled classes, because what a method calls is what the class file says. A
 * reading of the sources would answer the same question a second way, and would not see a call
 * written inside a lambda as the method that holds it.
 */
class OnlyAClaimSaysWhatAComparisonStatesTest {

    private static final String CANONICAL = "souther/compiler/check/CanonicalComparison";

    private static final String CLAIM = "souther/compiler/check/ComparisonClaim";

    /** Everything a canonical comparison is put together out of. A licence for one of these is a
     *  licence for none of the others: a reader allowed to deny a statement it did not make is a
     *  reader stating the comparison that holds exactly where the claim's does not. */
    private static final Set<String> ASSEMBLED =
            Set.of("theSameValue", "below", "denied");

    /** A method that may do this, and why it is the one that may. */
    private record Licence(String who, String why) { }

    private static final List<Licence> MAY_ASSEMBLE = List.of(
            new Licence("souther.compiler.check.ComparisonClaim.Cut.canonical",
                    "an order, with the sides the way the canonical form wants them and denied"
                            + " where the comparison holds at the value it names"),
            new Licence("souther.compiler.check.ComparisonClaim.Singled.canonical",
                    "an equality, denied where the comparison does not hold at the value it"
                            + " names — which is the same fact read the other way round"));

    private static final List<Licence> MAY_ASK = List.of(
            new Licence("souther.compiler.check.Conditions.canonical",
                    "keys a fact by the comparison a condition states, which is written as a node"
                            + " with what is asserted of it carried beside"),
            new Licence("souther.compiler.check.Terms.lambda$binary$0",
                    "names the value a comparison in a body is, which is written as a term"));

    /**
     * The derivation from what a comparison placed to what it states, which is the claim's own.
     *
     * <p>Two facts decide it and neither decides the other, so a reader putting them together is a
     * reader that remembers the pairing — and one that pairs them the other way round answers every
     * one of its own questions consistently about the comparison that holds where this one does
     * not.
     */
    @Test
    void onlyTheTwoClaimsPutACanonicalComparisonTogether() throws IOException {
        assertEquals(declared(MAY_ASSEMBLE), callsTo(CANONICAL, ASSEMBLED),
                "what a comparison states is derived where what it placed is held, and nowhere"
                        + " else. What each of these assembles: " + why(MAY_ASSEMBLE));
    }

    /**
     * And who asks for one, which is a consumer boundary and not the derivation.
     *
     * <p>Written down for the same reason the readers of an operator are: a reader appearing here
     * is one more place a comparison has to be written down in some representation, and what it
     * writes has to be a comparison of this compiler's own rather than one the source never wrote.
     */
    @Test
    void onlyAReaderWritingAComparisonDownAsksForOne() throws IOException {
        assertEquals(declared(MAY_ASK), callsTo(CLAIM, Set.of("canonical")),
                "asking a claim what it states is asking to write the comparison down somewhere."
                        + " What each of these writes it into: " + why(MAY_ASK));
    }

    private static Map<String, String> declared(List<Licence> licences) {
        Map<String, String> out = new TreeMap<>();
        licences.forEach(each -> out.put(each.who(), ""));
        return out;
    }

    private static Map<String, String> why(List<Licence> licences) {
        Map<String, String> out = new LinkedHashMap<>();
        licences.forEach(each -> out.put(each.who(), each.why()));
        return out;
    }

    /** Which methods of the compiler call any of {@code names} on {@code owner}. */
    private static Map<String, String> callsTo(String owner, Set<String> names) throws IOException {
        Map<String, String> calls = new TreeMap<>();
        int read = 0;
        for (Path each : classes()) {
            ClassModel model = ClassFile.of().parse(Files.readAllBytes(each));
            read++;
            String from = model.thisClass().asInternalName().replace('/', '.').replace('$', '.');
            for (MethodModel method : model.methods()) {
                method.code().ifPresent(code -> code.forEach(element -> {
                    if (element instanceof InvokeInstruction call
                            && call.owner().asInternalName().equals(owner)
                            && names.contains(call.name().stringValue())) {
                        calls.put(from + "." + method.methodName().stringValue(), "");
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
