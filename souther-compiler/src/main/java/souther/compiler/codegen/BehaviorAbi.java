package souther.compiler.codegen;

import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.MethodTypeDesc;
import java.util.Arrays;
import java.util.List;
import java.util.function.Function;

import static souther.compiler.codegen.Descriptors.CD_Behavior;
import static souther.compiler.codegen.Descriptors.CD_Object;

/**
 * How a behavior is held, applied and constructed on the JVM, as what it takes and answers decides
 * it.
 *
 * <p>One set of rules, read where a behavior's projection is made ({@link LinkageProjections}) and
 * where its own classes are emitted. Worked out twice, the classes a module declares and what it says
 * it provides would agree only until one of the two changed. A class of another module reads none of
 * this: it reads the projection.
 */
final class BehaviorAbi {

    private BehaviorAbi() {}

    /**
     * The type a class holds a behavior taking {@code takes} as, and takes it in its constructor as:
     * the unary {@code Behavior} for one taking one input, and its own class — the base Java extends,
     * or the interface of one with an implementation — for any other number of inputs.
     */
    static ClassDesc heldAs(ValueName.Behavior behavior, List<Type> takes) {
        return takes.size() == 1
                ? CD_Behavior
                : SoutherJvmAbi.nameOf(new GeneratedClass.BehaviorInterface(
                        behavior.module(), behavior.name())).classDesc();
    }

    /** The constructor of an implementation handed dependencies held as {@code held}, in order. */
    static MethodTypeDesc constructor(List<ClassDesc> held) {
        return MethodTypeDesc.of(ConstantDescs.CD_void, held.toArray(new ClassDesc[0]));
    }

    /** The {@code apply} taking and answering objects, which an implementation's body is on. */
    static MethodTypeDesc erasedApply(int arity) {
        ClassDesc[] params = new ClassDesc[arity];
        Arrays.fill(params, CD_Object);
        return MethodTypeDesc.of(CD_Object, params);
    }

    /**
     * The typed {@code apply} of a behavior taking {@code takes} and answering {@code answers}: each
     * mapped to the one reference class it is carried as ({@link #applyParamType}).
     *
     * @param resultUnion the class the behavior's output union is, where it answers one
     * @param classOf     the class of a declared type
     */
    static MethodTypeDesc typedApply(List<Type> takes, Type answers, ClassDesc resultUnion,
                                     Function<TypeSymbol, ClassDesc> classOf) {
        ClassDesc[] params = new ClassDesc[takes.size()];
        for (int i = 0; i < params.length; i++) {
            params[i] = applyParamType(takes.get(i), resultUnion, classOf);
        }
        return MethodTypeDesc.of(applyParamType(answers, resultUnion, classOf), params);
    }

    /**
     * The JVM reference type an {@code apply} slot takes for {@code t}: a collection keeps its raw
     * runtime interface ({@code java.util.List/Map/Set}, runtime {@code Option}); a union is the
     * behavior's result union; a declared type its class; a primitive its box; anything erased
     * (type variable, tuple, function) is {@code Object}.
     */
    static ClassDesc applyParamType(Type t, ClassDesc resultUnion,
                                    Function<TypeSymbol, ClassDesc> classOf) {
        if (t instanceof Type.ListOf || t instanceof Type.MapOf
                || t instanceof Type.SetOf || t instanceof Type.OptionOf) {
            return JvmTypes.jvmType(t, classOf);
        }
        ClassDesc r = refTypeOrNull(t, resultUnion, classOf);
        return r != null ? r : CD_Object;
    }

    /**
     * The single reference class {@code t} maps to where a behavior takes or answers it: the result
     * union for a union, the class of a declared type, the box of a primitive — or null for a
     * collection, which has no single class to name.
     */
    static ClassDesc refTypeOrNull(Type t, ClassDesc resultUnion,
                                   Function<TypeSymbol, ClassDesc> classOf) {
        if (t instanceof Type.Union) {
            return resultUnion;
        }
        if (t instanceof Type.Ref r) {
            return classOf.apply(r.name());
        }
        return JvmTypes.boxedPrim(t);
    }
}
