package souther.compiler.codegen;

import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.MethodTypeDesc;
import java.util.List;
import java.util.function.Function;

/**
 * How a behavior's implementation is constructed on the JVM: the constructor its class declares,
 * as the behaviors it is handed decide it.
 *
 * <p>One rule, read by the emitter that declares the constructor and links against it, and by the
 * check that holds a module read off the path to what it was built against. Worked out twice, the
 * check would be restating how the emitter chooses a parameter type, and the two would agree only
 * until one of them changed.
 */
public final class ConstructionAbi {

    private ConstructionAbi() {}

    /**
     * The type a class holds {@code dependency} as, and takes it in its constructor as: the unary
     * {@code Behavior} for one taking one input, and its own class — the base Java extends, or the
     * interface of one with an implementation — for any other number of inputs.
     */
    static ClassDesc heldAs(ValueName.Behavior dependency, List<Type> takes) {
        return takes.size() == 1
                ? Descriptors.CD_Behavior
                : SoutherJvmAbi.nameOf(new GeneratedClass.BehaviorInterface(
                        dependency.module(), dependency.name())).classDesc();
    }

    /**
     * The constructor of an implementation handed {@code dependencies} in that order, each taking
     * what {@code takes} says it does.
     */
    public static MethodTypeDesc constructor(List<ValueName.Behavior> dependencies,
                                             Function<ValueName.Behavior, List<Type>> takes) {
        ClassDesc[] params = new ClassDesc[dependencies.size()];
        for (int i = 0; i < params.length; i++) {
            params[i] = heldAs(dependencies.get(i), takes.apply(dependencies.get(i)));
        }
        return MethodTypeDesc.of(ConstantDescs.CD_void, params);
    }
}
