package souther.compiler.codegen;

import net.unit8.raoh.ErrorCodes;
import souther.compiler.core.BoundaryConstraint;

import java.lang.classfile.ClassBuilder;
import java.lang.classfile.ClassFile;
import java.lang.classfile.CodeBuilder;
import java.lang.classfile.Label;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.DirectMethodHandleDesc;
import java.lang.constant.MethodHandleDesc;
import java.lang.constant.MethodTypeDesc;

import static souther.compiler.codegen.Descriptors.CD_Integer;
import static souther.compiler.codegen.Descriptors.CD_Map;
import static souther.compiler.codegen.Descriptors.CD_RDecoder;
import static souther.compiler.codegen.Descriptors.CD_RPath;
import static souther.compiler.codegen.Descriptors.CD_RResult;
import static souther.compiler.codegen.Descriptors.CD_String;
import static souther.compiler.codegen.Descriptors.MTD_Rok;
import static souther.compiler.codegen.Descriptors.MTD_flatMapWithPath;
import static souther.compiler.codegen.Descriptors.MTD_invariantFailure;

/**
 * A map's entry-count constraints, as the issue Raoh reports for them.
 *
 * <p>Checked on the map the model declares — its keys decoded and canonical — because that is the
 * value the clauses are about, and the clauses of one newtype are checked in the order they are
 * declared on one value. Raoh's own {@code minSize} and {@code maxSize} are on the decoder of a
 * string-keyed object, which is the map before its keys are decoded, so they are not what runs here.
 * What runs is the generic step every decoder has ({@code flatMapWithPath}), failing with the issue
 * Raoh's constraint fails with: {@code too_small} with {@code min} and {@code actual}, {@code too_big}
 * with {@code max} and {@code actual}, and Raoh's default message.
 *
 * <p>That issue is written out here, and so it is a copy of Raoh's. Which constraint a clause is was
 * decided by the checker; this only says what Raoh calls it, and a Raoh that came to call it
 * something else is caught by the test that holds the two issues equal.
 */
final class RaohMapSizes {

    private static final String AT_LEAST = "__mapMinSize";
    private static final String AT_MOST = "__mapMaxSize";

    /** {@code static Result helper(int bound, Object map, Path path)}. */
    private static final MethodTypeDesc MTD_sizeCheck =
            MethodTypeDesc.of(CD_RResult, ConstantDescs.CD_int, ConstantDescs.CD_Object, CD_RPath);

    private RaohMapSizes() {}

    /**
     * Chains {@code constraint} onto the decoder on the stack, which answers the map the model
     * declares, leaving the decoder that fails where the map breaks it.
     */
    static void emit(CodeBuilder code, ClassDesc decoderClass, BoundaryConstraint.OfMap constraint) {
        switch (constraint) {
            case BoundaryConstraint.MapMinSize m -> chain(code, decoderClass, AT_LEAST, m.n());
            case BoundaryConstraint.MapMaxSize m -> chain(code, decoderClass, AT_MOST, m.n());
        }
    }

    private static void chain(CodeBuilder code, ClassDesc decoderClass, String helper, int bound) {
        code.loadConstant(bound);
        DirectMethodHandleDesc impl = MethodHandleDesc.ofMethod(
                DirectMethodHandleDesc.Kind.STATIC, decoderClass, helper, MTD_sizeCheck);
        code.invokedynamic(Lambdas.callSite(Lambdas.Sam.BI_FUNCTION, impl, MTD_invariantFailure,
                ConstantDescs.CD_int));                                          // captures the bound
        code.invokeinterface(CD_RDecoder, "flatMapWithPath", MTD_flatMapWithPath);
    }

    /** Emits the two helpers {@link #emit} chains, onto the decoder class being built. */
    static void emitHelpers(ClassBuilder cb) {
        emitHelper(cb, AT_LEAST, ErrorCodes.TOO_SMALL, "min", "must have at least ");
        emitHelper(cb, AT_MOST, ErrorCodes.TOO_BIG, "max", "must have at most ");
    }

    /**
     * {@code static Result helper(int bound, Object map, Path path)}: the map where its size is on
     * the right side of {@code bound}, and otherwise
     * {@code Result.failWith(path, code, null, message, Map.of(bound key, bound, "actual", size))}.
     *
     * <p>The message is Raoh's default, {@code "must have at least %d entries"} and its upper
     * counterpart. A {@code %d} of an {@code int} writes what {@code Integer.toString} writes, so the
     * text is joined rather than formatted.
     */
    private static void emitHelper(ClassBuilder cb, String name, String errorCode, String boundKey,
                                   String messageHead) {
        boolean atLeast = name.equals(AT_LEAST);
        cb.withMethodBody(name, MTD_sizeCheck, ClassFile.ACC_STATIC | ClassFile.ACC_SYNTHETIC,
                code -> {
            int size = 3;
            code.aload(1);
            code.checkcast(CD_Map);
            code.invokeinterface(CD_Map, "size", MethodTypeDesc.of(ConstantDescs.CD_int));
            code.istore(size);
            Label broken = code.newLabel();
            code.iload(size);
            code.iload(0);
            if (atLeast) {
                code.if_icmplt(broken);
            } else {
                code.if_icmpgt(broken);
            }
            code.aload(1);
            code.invokestatic(CD_RResult, "ok", MTD_Rok, true);
            code.areturn();
            code.labelBinding(broken);
            code.aload(2);                                                // path
            code.loadConstant(errorCode);
            code.aconst_null();                                           // no custom message
            code.loadConstant(messageHead);
            code.iload(0);
            code.invokestatic(CD_Integer, "toString",
                    MethodTypeDesc.of(CD_String, ConstantDescs.CD_int));
            code.invokevirtual(CD_String, "concat", MethodTypeDesc.of(CD_String, CD_String));
            code.loadConstant(" entries");
            code.invokevirtual(CD_String, "concat", MethodTypeDesc.of(CD_String, CD_String));
            code.loadConstant(boundKey);
            code.iload(0);
            code.invokestatic(CD_Integer, "valueOf", MethodTypeDesc.of(CD_Integer, ConstantDescs.CD_int));
            code.loadConstant("actual");
            code.iload(size);
            code.invokestatic(CD_Integer, "valueOf", MethodTypeDesc.of(CD_Integer, ConstantDescs.CD_int));
            code.invokestatic(CD_Map, "of", MethodTypeDesc.of(CD_Map, ConstantDescs.CD_Object,
                    ConstantDescs.CD_Object, ConstantDescs.CD_Object, ConstantDescs.CD_Object), true);
            code.invokestatic(CD_RResult, "failWith", MethodTypeDesc.of(CD_RResult, CD_RPath,
                    CD_String, CD_String, CD_String, CD_Map), true);
            code.areturn();
        });
    }
}
