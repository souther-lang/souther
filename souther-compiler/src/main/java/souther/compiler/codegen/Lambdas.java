package souther.compiler.codegen;

import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.DirectMethodHandleDesc;
import java.lang.constant.DynamicCallSiteDesc;
import java.lang.constant.MethodHandleDesc;
import java.lang.constant.MethodTypeDesc;

import static souther.compiler.codegen.Descriptors.*;

/**
 * A method made into an instance of a functional interface at an {@code invokedynamic}, which is
 * what {@code LambdaMetafactory} does.
 *
 * <p>What a call site says is which interface, which method stands behind it, what it captures
 * and the type the method is used at. The bootstrap, the type the call site is invoked at and the
 * order the arguments go in are the JVM's protocol, and are written here once.
 */
final class Lambdas {

    private Lambdas() {}

    /**
     * A functional interface as the metafactory is told about it: the interface, the name of its
     * one abstract method and that method's erased type.
     *
     * <p>A closed set because the three are one fact about the interface. Handed over apart, a
     * call site could ask for {@code encode} on a {@code Function}, which links to nothing.
     */
    enum Sam {
        FUNCTION(CD_Function, "apply", MethodTypeDesc.of(CD_Object, CD_Object)),
        BI_FUNCTION(CD_BiFunction, "apply", MethodTypeDesc.of(CD_Object, CD_Object, CD_Object)),
        PREDICATE(CD_Predicate, "test", MethodTypeDesc.of(ConstantDescs.CD_boolean, CD_Object)),
        TO_INT_FUNCTION(CD_ToIntFunction, "applyAsInt",
                MethodTypeDesc.of(ConstantDescs.CD_int, CD_Object)),
        ENCODER(CD_REncoder, "encode", MTD_Rencode);

        private final ClassDesc type;
        private final String method;
        private final MethodTypeDesc erased;

        Sam(ClassDesc type, String method, MethodTypeDesc erased) {
            this.type = type;
            this.method = method;
            this.erased = erased;
        }
    }

    /** {@code LambdaMetafactory.metafactory}. */
    private static final DirectMethodHandleDesc METAFACTORY = MethodHandleDesc.ofMethod(
            DirectMethodHandleDesc.Kind.STATIC,
            ClassDesc.of("java.lang.invoke.LambdaMetafactory"), "metafactory",
            MethodTypeDesc.of(ConstantDescs.CD_CallSite, ConstantDescs.CD_MethodHandles_Lookup,
                    ConstantDescs.CD_String, ConstantDescs.CD_MethodType,
                    ConstantDescs.CD_MethodType, ConstantDescs.CD_MethodHandle,
                    ConstantDescs.CD_MethodType));

    /**
     * The call site that makes {@code implementation}, used at {@code instantiated}, into a
     * {@code sam}, taking {@code captures} off the stack as it does.
     */
    static DynamicCallSiteDesc callSite(Sam sam, DirectMethodHandleDesc implementation,
                                        MethodTypeDesc instantiated, ClassDesc... captures) {
        return DynamicCallSiteDesc.of(METAFACTORY, sam.method,
                MethodTypeDesc.of(sam.type, captures), sam.erased, implementation, instantiated);
    }
}
