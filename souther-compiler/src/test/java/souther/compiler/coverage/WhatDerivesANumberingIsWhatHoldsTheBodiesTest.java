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
 * A module's numbering is derived where its bodies are held, and nowhere else in the compiler.
 *
 * <p>{@link CoverageSites#of} is a function of the bodies, so two calls of it over one module come
 * to one numbering. That is what a reader takes on trust when it derives its own: the emitter wrote
 * numbers into probe calls under one plan, and a measure looks a hit up under another, and the two
 * are about one place only while the walk keeps agreeing with itself. Which is a property to hold
 * rather than a thing to rely on quietly — and the fewer places derive one, the less of the
 * compiler that property has to hold across.
 *
 * <p>So what is fixed here is not that the numbering is right; it is who may ask for one. A reader
 * that wants to know what a hit set means asks the check that holds the bodies, and there is one
 * such check per module. A second derivation somewhere else is a second answer that no later check
 * could tell from the first, since both are true of the same bodies until one of them stops being.
 *
 * <p><b>Who derives one, not who has one.</b> A method that asks the check for the module's
 * numbering is not counted here and is not meant to be: it takes the answer the bodies' own holder
 * gives, which is the whole of what this fixes. So a second way of <em>reaching</em> that answer —
 * a helper elsewhere that asks the check and hands the plan on — stays green under this. What is
 * wrong with such a helper is that a reader then has two routes to one answer, not that the two
 * could disagree.
 *
 * <p>Read off the compiled classes, so what is counted is what a method does rather than what a
 * reading of the sources makes of it — a call written inside a lambda belongs to the lambda, and
 * this says so.
 *
 * <p><b>What it does not see, said rather than left to be found.</b> The tests are not in
 * {@code target/classes}: a test deriving a plan straight from bodies is a fixture standing in for
 * a compile, and there is no reader downstream of it to disagree with. And what is read is this
 * module's classes — a caller written in the CLI or the language server would not be counted here.
 * Widening it is not free: those modules are built after this one, so a walk over their output
 * would read whatever the last build left and would say nothing at all on a clean one.
 */
class WhatDerivesANumberingIsWhatHoldsTheBodiesTest {

    private static final String SITES = "souther/compiler/coverage/CoverageSites";

    /** A method that may derive one, how many times it does, and why it is one of the ones that
     *  does. */
    private record Licence(String who, int calls, String why) { }

    private static final List<Licence> MAY_DERIVE = List.of(
            new Licence("souther.compiler.query.Bodies.judged", 1,
                    "what a body claims cannot arrive is judged against the arms of the same"
                            + " bodies, and the claim and the reading that judges it have to name"
                            + " one arm"),
            new Licence("souther.compiler.query.Bodies.Elaborated.plan", 1,
                    "what every reader outside the check asks: the bodies are held here, so this is"
                            + " where a numbering of them is a numbering of anything at all"));

    @Test
    void onlyTheCheckThatHoldsThemDerivesAModulesNumbering() throws IOException {
        assertEquals(declared(), derivations(),
                "a numbering derived anywhere else is a second answer about one module's arms, and"
                        + " a reader holding it is reading a run against numbers nothing wrote."
                        + " What may derive one, and why: " + why());
    }

    private static Map<String, Integer> declared() {
        Map<String, Integer> out = new TreeMap<>();
        MAY_DERIVE.forEach(each -> out.put(each.who(), each.calls()));
        return out;
    }

    private static Map<String, String> why() {
        Map<String, String> out = new LinkedHashMap<>();
        MAY_DERIVE.forEach(each -> out.put(each.who(), each.why()));
        return out;
    }

    /** How many times each method of the compiler derives a numbering. */
    private static Map<String, Integer> derivations() throws IOException {
        Map<String, Integer> calls = new TreeMap<>();
        int read = 0;
        for (Path each : classes()) {
            ClassModel model = ClassFile.of().parse(Files.readAllBytes(each));
            read++;
            String from = model.thisClass().asInternalName().replace('/', '.').replace('$', '.');
            for (MethodModel method : model.methods()) {
                method.code().ifPresent(code -> code.forEach(element -> {
                    if (element instanceof InvokeInstruction call
                            && call.owner().asInternalName().equals(SITES)
                            && call.name().stringValue().equals("of")) {
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
