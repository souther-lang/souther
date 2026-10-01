package souther.architecture;

import souther.test.OnItsOwnStack;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.constant.MethodTypeDesc;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A test that runs work on a stack of its own does it through {@link OnItsOwnStack}, and nothing
 * else in the tests starts such a thread.
 *
 * <p>A test about how deep something goes runs work it means to be large, and whether that work
 * comes back at all is part of what it asks. Written by hand, each test decides for itself how long
 * to wait, and a wait with no end answers a compiler that never comes back by never coming back
 * either. The door is where the wait is bounded, once; a test that goes round it has a wait of its
 * own again.
 *
 * <p>Read off the class files, as a call to a {@code Thread} constructor that takes a stack size or
 * to the platform thread builder's {@code stackSize}. The population is every module's tests and
 * the classes those tests are given to share, which is where the door itself is — so the door is
 * found by the same reading, which is what says the reading sees such a call at all.
 */
class ATestRunsWorkOnAStackOfItsOwnOnlyThroughOneDoorTest {

    private static final CompiledOutputs OUTPUTS = CompiledOutputs.ofEverythingCompiledHere();

    private static final String THREAD = "java/lang/Thread";

    private static final String PLATFORM_BUILDER = "java/lang/Thread$Builder$OfPlatform";

    private static final Set<String> WITH_A_STACK_SIZE = Set.of(
            "(Ljava/lang/ThreadGroup;Ljava/lang/Runnable;Ljava/lang/String;J)V",
            "(Ljava/lang/ThreadGroup;Ljava/lang/Runnable;Ljava/lang/String;JZ)V");

    @Test
    void onlyTheDoorStartsAThreadWithAStackOfItsOwn() {
        TreeSet<String> starting = new TreeSet<>();
        for (ClassModel each : population()) {
            for (MethodModel method : each.methods()) {
                if (startsAThreadWithAStack(method)) {
                    starting.add(each.thisClass().asInternalName().replace('/', '.'));
                }
            }
        }

        assertEquals(List.of(OnItsOwnStack.class.getName()), List.copyOf(starting),
                "a test starts a thread with a stack of its own other than through "
                        + OnItsOwnStack.class.getSimpleName() + ", so how long it waits is its own"
                        + " to decide again");
    }

    private static List<ClassModel> population() {
        List<ClassModel> found = new ArrayList<>();
        for (Path module : OUTPUTS.modules()) {
            found.addAll(OUTPUTS.testClassesOf(module));
        }
        found.addAll(OUTPUTS.classesOf(OUTPUTS.module("souther-test-support")));
        return found;
    }

    private static boolean startsAThreadWithAStack(MethodModel method) {
        return method.code().stream()
                .flatMap(code -> code.elementStream())
                .anyMatch(element -> element instanceof InvokeInstruction call
                        && takesAStackSize(call));
    }

    private static boolean takesAStackSize(InvokeInstruction call) {
        String owner = call.owner().asInternalName();
        String name = call.name().stringValue();
        MethodTypeDesc type = call.typeSymbol();
        return (owner.equals(THREAD) && name.equals("<init>")
                        && WITH_A_STACK_SIZE.contains(type.descriptorString()))
                || (owner.equals(PLATFORM_BUILDER) && name.equals("stackSize"));
    }
}
