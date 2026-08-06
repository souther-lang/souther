package souther.compiler.evaluate;

import java.lang.classfile.ClassFile;
import java.lang.classfile.CodeBuilder;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeTransform;
import java.lang.classfile.Label;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.BranchInstruction;
import java.lang.classfile.instruction.LabelTarget;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.MethodTypeDesc;
import java.util.HashSet;
import java.util.Set;

/**
 * A class that was compiled elsewhere, counted.
 *
 * <p>What a compilation generates it counts as it emits, because it knows where the loops are. What
 * it reads off the module path it did not emit, and a published module carries only what an importer
 * needs to read its declarations — its types, its invariants, the {@code let}s it exposes. A
 * behavior's body stays in the jar it was built into. So a row that reaches one used to run code with
 * no counted point in it: the budget stopped at the import, and what bounded the row was the wait.
 *
 * <p>Counting it here rather than asking the artifact to carry more. Publishing bodies would change
 * what a jar holds and make an implementation readable by everyone who imports it, for the sake of a
 * measurement; rewriting the bytecode changes nothing anyone ships and works on jars that were built
 * before any of this existed.
 *
 * <p>Every backward branch is counted, which is every loop the class has however it was written. A
 * branch to a label already passed is going round again; a branch forward is a conditional or a join
 * and costs nothing. That is the same rule the emitter follows for the code it writes itself, applied
 * to code whose shape is no longer in hand.
 *
 * <p>What this cannot add is the recursion depth count, which the emitter puts in by moving a
 * helper's body aside and wrapping it. A recursion in a class read from a jar is bounded by the stack
 * the evaluation runs on and reported as having exhausted it, rather than by the depth limit.
 */
public final class Recounted {

    private static final ClassDesc CD_CONTEXT = ClassDesc.of(EvaluationContext.class.getName());
    private static final MethodTypeDesc MTD_TICK = MethodTypeDesc.of(ConstantDescs.CD_void);

    /**
     * {@code bytes}, with a counted point on every backward branch.
     *
     * <p>Returns the bytes unchanged where they cannot be read as a class file. A jar holding
     * something this cannot parse is not a reason to refuse to evaluate: uncounted is what the code
     * was before, and the wait still bounds it.
     */
    public static byte[] of(byte[] bytes) {
        try {
            ClassFile classFile = ClassFile.of();
            // A transform of its own per method: which branches go backward is a fact about one
            // method's labels, and a transform shared between two of them would carry the first
            // one's labels into the second.
            java.lang.classfile.ClassTransform counting = (builder, element) -> {
                if (element instanceof MethodModel method) {
                    builder.transformMethod(method,
                            java.lang.classfile.MethodTransform.transformingCode(countingCode()));
                } else {
                    builder.with(element);
                }
            };
            return classFile.transformClass(classFile.parse(bytes), counting);
        } catch (RuntimeException _) {
            return bytes;
        }
    }

    /** Whether {@code bytes} names the counting context, i.e. has already been through here or was
     * generated counted. Read by tests that hold the two apart. */
    public static boolean counts(byte[] bytes) {
        try {
            for (java.lang.classfile.constantpool.PoolEntry entry
                    : ClassFile.of().parse(bytes).constantPool()) {
                if (entry instanceof java.lang.classfile.constantpool.ClassEntry named
                        && named.asInternalName().equals(CD_CONTEXT.packageName().replace('.', '/')
                                + "/" + CD_CONTEXT.displayName())) {
                    return true;
                }
            }
            return false;
        } catch (RuntimeException _) {
            return false;
        }
    }

    /**
     * One method's code, with the counted points put in.
     *
     * <p>Which branches go backward is not known until the method has been read, and a transform sees
     * its elements once — so the labels already passed are remembered as they go by, and a branch to
     * one of them is a branch going round again.
     */
    private static CodeTransform countingCode() {
        Set<Label> passed = new HashSet<>();
        return new CodeTransform() {
            @Override
            public void accept(CodeBuilder builder, CodeElement element) {
                if (element instanceof LabelTarget target) {
                    passed.add(target.label());
                    builder.with(element);
                    return;
                }
                if (element instanceof BranchInstruction branch && passed.contains(branch.target())) {
                    builder.invokestatic(CD_CONTEXT, "tick", MTD_TICK);
                }
                builder.with(element);
            }
        };
    }

    private Recounted() {}
}
