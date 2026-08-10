package souther.compiler.codegen;

import souther.compiler.check.MatchElaborator;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.lang.classfile.CodeBuilder;
import java.lang.classfile.Label;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.MethodTypeDesc;
import java.util.List;

import static souther.compiler.codegen.Descriptors.*;

/**
 * The two conversions between a Souther value and a behavior's result union as the JVM carries it.
 *
 * <p>A member a module declared is the union's case itself. A primitive and a type another module
 * emitted cannot implement an interface declared here, so they reach the union through a bridge case
 * (spec §jvm-anonymous-union). That leaves the union with two forms, and this is where they meet:
 *
 * <ul>
 *   <li>{@link #inject} — a behavior returns, and the Souther value it answers with becomes a member
 *       of its declared union.
 *   <li>{@link #project} — a caller receives that member and reads a Souther value out of it.
 * </ul>
 *
 * <p>Inside a body every value is a Souther value, so {@code inject} never sees a bridge case and no
 * value is wrapped twice. Both walk the union's members, which are known where they are emitted, so
 * neither asks a value whether it happens to be wrapped.
 *
 * <p>{@code project(inject(v))} is {@code v}.
 */
final class ResultBoundary {

    private ResultBoundary() {}

    /** Returns the value on the stack as a member of {@code members}' union. */
    static void inject(CodeBuilder code, CodegenContext ctx, List<TypeName> bridged, int slot) {
        if (bridged.isEmpty()) {
            code.areturn();
            return;
        }
        code.astore(slot);
        for (TypeName member : bridged) {
            Label next = code.newLabel();
            code.aload(slot);
            code.instanceOf(ctx.matchCaseClass(member));
            code.ifeq(next);
            ClassDesc bridge = ctx.bridgeCaseClass(member);
            Type held = MatchElaborator.caseBindType(member);
            code.new_(bridge);
            code.dup();
            code.aload(slot);
            unwrapTo(code, held, ctx);
            code.invokespecial(bridge, "<init>",
                    MethodTypeDesc.of(ConstantDescs.CD_void, JvmTypes.jvmType(held, ctx)));
            code.areturn();
            code.labelBinding(next);
        }
        code.aload(slot);
        code.areturn();
    }

    /** Reads the Souther value out of the union member on the stack, leaving it boxed. */
    static void project(CodeBuilder code, CodegenContext ctx, String callee, List<TypeName> bridged,
                        int slot) {
        if (bridged.isEmpty()) {
            return;
        }
        code.astore(slot);
        Label done = code.newLabel();
        for (TypeName member : bridged) {
            Label next = code.newLabel();
            ClassDesc bridge = ctx.bridgeCaseClassOf(callee, member);
            code.aload(slot);
            code.instanceOf(bridge);
            code.ifeq(next);
            code.aload(slot);
            code.checkcast(bridge);
            Type held = MatchElaborator.caseBindType(member);
            code.invokevirtual(bridge, "value", MethodTypeDesc.of(JvmTypes.jvmType(held, ctx)));
            JvmTypes.box(code, held);
            code.goto_(done);
            code.labelBinding(next);
        }
        code.aload(slot);
        code.labelBinding(done);
    }

    /** Casts the {@code Object} on the stack to what a bridge case holds, unboxing a primitive. */
    private static void unwrapTo(CodeBuilder code, Type held, CodegenContext ctx) {
        if (held == Type.INT) {
            code.checkcast(CD_Long);
            code.invokevirtual(CD_Long, "longValue", MethodTypeDesc.of(ConstantDescs.CD_long));
        } else if (held == Type.BOOL) {
            code.checkcast(CD_Boolean);
            code.invokevirtual(CD_Boolean, "booleanValue", MethodTypeDesc.of(ConstantDescs.CD_boolean));
        } else {
            code.checkcast(JvmTypes.jvmType(held, ctx));
        }
    }
}
