package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.constant.ConstantDesc;
import java.lang.constant.DirectMethodHandleDesc;
import java.lang.constant.MethodTypeDesc;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The compiler's own code calls a runtime operation by the entry that takes a checkpoint, wherever
 * the runtime has one, and hands it the evaluation's.
 *
 * <p>What the compiler runs during an evaluation — comparing what a row stated with what came back,
 * putting a fixture's set together — goes over values the evaluation built, as the evaluated code
 * does, and a call by the entry without a checkpoint is work the evaluation cannot stop. Asked of the
 * whole compiler rather than of the classes an evaluation is thought to reach: outside one, the
 * checkpoint the compiler hands in is the one nobody holds, so the rule costs a lookup there and a
 * call added later in a class nobody thought of is held to it all the same. Which operations have
 * such an entry is read off the runtime's own class files.
 */
class TheCompilerCallsARuntimeOperationWithTheCheckpointItTakesTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String CHECKPOINT = "Lsouther/runtime/WorkCheckpoint;";

    @Test
    void noCompilerClassReachesTheEntryWithoutTheCheckpoint() {
        Set<String> withoutTheCheckpoint = entriesThatHaveACountedTwin();
        assertTrue(withoutTheCheckpoint.size() > 50,
                "the runtime's entries with a counted twin were read: " + withoutTheCheckpoint.size());
        TreeSet<String> found = new TreeSet<>();
        for (ClassModel owner : COMPILED.classesOf(COMPILED.module("souther-compiler"))) {
            for (MethodModel method : owner.methods()) {
                if (method.code().isEmpty()) {
                    continue;
                }
                for (CodeElement element : method.code().get()) {
                    for (String reached : reached(element)) {
                        if (withoutTheCheckpoint.contains(reached)) {
                            found.add(AMethod.of(owner, method) + " reaches " + reached);
                        }
                    }
                }
            }
        }
        assertEquals(List.of(), List.copyOf(found));
    }

    /** Every runtime static that has a twin of the same name taking what it takes and a checkpoint
     *  last, as {@code owner#name(descriptor)}. */
    private static Set<String> entriesThatHaveACountedTwin() {
        Set<String> counted = new HashSet<>();
        List<String> all = new ArrayList<>();
        for (ClassModel owner : COMPILED.classesOf(COMPILED.module("souther-runtime"))) {
            String name = owner.thisClass().asInternalName();
            for (MethodModel method : owner.methods()) {
                String key = name + "#" + method.methodName().stringValue() + method.methodType().stringValue();
                all.add(key);
                if (method.methodType().stringValue().contains(CHECKPOINT + ")")) {
                    counted.add(key);
                }
            }
        }
        Set<String> out = new HashSet<>();
        for (String key : all) {
            int close = key.lastIndexOf(')');
            if (counted.contains(key.substring(0, close) + CHECKPOINT + key.substring(close))) {
                out.add(key);
            }
        }
        return out;
    }

    /** The runtime methods {@code element} calls or binds, as {@code owner#name(descriptor)}. */
    private static List<String> reached(CodeElement element) {
        List<String> out = new ArrayList<>();
        if (element instanceof InvokeInstruction invoke) {
            out.add(invoke.owner().asInternalName() + "#" + invoke.name().stringValue()
                    + invoke.type().stringValue());
        } else if (element instanceof InvokeDynamicInstruction indy) {
            for (ConstantDesc argument : indy.bootstrapArgs()) {
                if (argument instanceof DirectMethodHandleDesc handle) {
                    String owner = handle.owner().descriptorString();
                    MethodTypeDesc type = handle.invocationType();
                    out.add(owner.substring(1, owner.length() - 1) + "#" + handle.methodName()
                            + type.descriptorString());
                }
            }
        }
        return out;
    }
}
