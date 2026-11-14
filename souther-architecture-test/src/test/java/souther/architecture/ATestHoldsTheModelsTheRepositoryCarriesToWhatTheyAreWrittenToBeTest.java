package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.constantpool.ClassEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.lang.classfile.instruction.InvokeInstruction;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A test that takes models from {@code RepositoryModels} does not hold them to compile.
 *
 * <p>The population includes corpora that are written to be refused, and a model that is refused as
 * it was written to be is a model that does not compile. Held to compile, such a test passes in the
 * run a change waits on only because it is not in that run: these tests are asked at night. What a
 * model of the population is held to is what it is written to be, and that is asked of
 * {@code RepositoryModels.refusedWith}, or taken from the analysis that already holds it
 * ({@code ConformanceCorpus.Analysed#answered}).
 *
 * <p>Read off the class files, per method: one that reaches the population and also calls
 * {@code ACompiledModel.compiles} on a compilation is found, with the lambdas javac made of its
 * body. A model the test makes itself is held to compile in a method that does not reach the
 * population, which is where it belongs. What this cannot see is a compilation handed from one
 * method to another and held to compile there; it is not a data-flow check.
 */
class ATestHoldsTheModelsTheRepositoryCarriesToWhatTheyAreWrittenToBeTest {

    private static final CompiledOutputs OUTPUTS = CompiledOutputs.ofEverythingCompiledHere();

    private static final String POPULATION = "souther/compiler/conformance/RepositoryModels";

    /** The calls of it that hand out a model, as opposed to what a model already knows. */
    private static final Set<String> HANDS_OUT = Set.of("all", "byCorpus", "conformance", "analysed");

    private static final String HELPER = "souther/compiler/ACompiledModel";

    private static final String COMPILES_A_COMPILATION =
            "(Lsouther/compiler/query/Compilation;)Lsouther/compiler/query/Compilation;";

    @Test
    void noMethodThatTakesAModelFromThePopulationHoldsOneToCompile() {
        Set<String> holding = new TreeSet<>();
        int reaching = 0;
        for (ClassModel each : population()) {
            if (!names(each, POPULATION)) {
                continue;
            }
            List<MethodModel> methods = each.methods();
            for (MethodModel method : methods) {
                String name = method.methodName().stringValue();
                if (name.startsWith("lambda$") || !callsOneOf(method, POPULATION, HANDS_OUT)) {
                    continue;
                }
                reaching++;
                String owner = each.thisClass().asInternalName();
                for (MethodModel body : methods) {
                    if (isWrittenInside(body, name) && holdsToCompile(body)) {
                        holding.add(owner.replace('/', '.') + "#" + name);
                    }
                }
            }
        }
        assertTrue(reaching > 0,
                "no method reaches " + POPULATION + ", so the name is stale and this holds for a"
                        + " reason other than the one it states");
        assertEquals(List.of(), List.copyOf(holding),
                "a method that takes a model from " + POPULATION + " holds a compilation to"
                        + " compile, which a corpus written to be refused does not: hold it to"
                        + " refusedWith(RepositoryModels.refusedWith(model), model)");
    }

    /**
     * Whether the class names {@code target} in its constant pool, which is read without decoding
     * a method. A class that does not name the population calls none of it.
     */
    private static boolean names(ClassModel candidate, String target) {
        for (PoolEntry entry : candidate.constantPool()) {
            if (entry instanceof ClassEntry it && it.asInternalName().equals(target)) {
                return true;
            }
        }
        return false;
    }

    /** The method itself, or a lambda javac made of what is written in it. */
    private static boolean isWrittenInside(MethodModel candidate, String method) {
        String name = candidate.methodName().stringValue();
        return name.equals(method) || name.startsWith("lambda$" + method + "$");
    }

    private static boolean holdsToCompile(MethodModel method) {
        return method.code().stream().flatMap(code -> code.elementStream())
                .anyMatch(element -> element instanceof InvokeInstruction call
                        && call.owner().asInternalName().equals(HELPER)
                        && call.name().stringValue().equals("compiles")
                        && call.typeSymbol().descriptorString().equals(COMPILES_A_COMPILATION));
    }

    private static boolean callsOneOf(MethodModel method, String owner, Set<String> names) {
        return method.code().stream().flatMap(code -> code.elementStream())
                .anyMatch(element -> element instanceof InvokeInstruction call
                        && call.owner().asInternalName().equals(owner)
                        && names.contains(call.name().stringValue()));
    }

    private static List<ClassModel> population() {
        List<ClassModel> found = new ArrayList<>();
        for (Path module : OUTPUTS.modules()) {
            found.addAll(OUTPUTS.testClassesOf(module));
        }
        return found;
    }
}
