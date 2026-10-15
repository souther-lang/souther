package souther.architecture;

import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.constant.ConstantDesc;
import java.lang.constant.DirectMethodHandleDesc;
import java.lang.reflect.AccessFlag;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * Which method of a class each of its lambdas is written in.
 *
 * <p>A lambda is compiled into a synthetic method of its own, so what its body does is found in
 * that method and not in the one it is written in. A check that answers per method answers for the
 * method the author wrote, which is the one holding the instruction that makes the lambda — and,
 * where that is a lambda too, the one holding that.
 */
final class WhereALambdaIsWritten {

    /** The handles that name a field rather than a method, which no lambda is. */
    private static final Set<DirectMethodHandleDesc.Kind> FIELD_HANDLES = Set.of(
            DirectMethodHandleDesc.Kind.GETTER, DirectMethodHandleDesc.Kind.SETTER,
            DirectMethodHandleDesc.Kind.STATIC_GETTER, DirectMethodHandleDesc.Kind.STATIC_SETTER);

    private final Map<String, String> writtenIn;

    private WhereALambdaIsWritten(Map<String, String> writtenIn) {
        this.writtenIn = writtenIn;
    }

    /**
     * The lambdas of {@code owner}: the synthetic methods a handle of an instruction of it names. A
     * method named by a method reference is not one, and is answered for as itself.
     */
    static WhereALambdaIsWritten in(ClassModel owner) {
        String self = owner.thisClass().asInternalName();
        Set<String> synthetic = new HashSet<>();
        for (MethodModel method : owner.methods()) {
            if (method.flags().has(AccessFlag.SYNTHETIC)) {
                synthetic.add(AMethod.of(owner, method));
            }
        }
        Map<String, String> out = new HashMap<>();
        for (MethodModel method : owner.methods()) {
            method.code().ifPresent(code -> code.elementList().forEach(element -> {
                if (!(element instanceof InvokeDynamicInstruction indy)) {
                    return;
                }
                for (ConstantDesc arg : indy.bootstrapArgs()) {
                    if (arg instanceof DirectMethodHandleDesc handle
                            && !FIELD_HANDLES.contains(handle.kind())
                            && internalNameOf(handle.owner().descriptorString()).equals(self)) {
                        String made = AMethod.of(self, handle.methodName(),
                                handle.lookupDescriptor());
                        if (synthetic.contains(made)) {
                            out.put(made, AMethod.of(owner, method));
                        }
                    }
                }
            }));
        }
        return new WhereALambdaIsWritten(out);
    }

    /** The method {@code method} is written in, through every lambda it is written in. */
    String enclosing(String method) {
        String at = method;
        Set<String> met = new HashSet<>();
        while (writtenIn.containsKey(at) && met.add(at)) {
            at = writtenIn.get(at);
        }
        return at;
    }

    private static String internalNameOf(String descriptor) {
        return descriptor.substring(1, descriptor.length() - 1);
    }
}
