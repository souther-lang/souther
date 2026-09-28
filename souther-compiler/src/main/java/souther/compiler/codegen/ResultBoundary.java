package souther.compiler.codegen;

import souther.compiler.check.TypeOps;
import souther.compiler.jvm.LinkageProjection;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.lang.classfile.CodeBuilder;
import java.lang.classfile.Label;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.MethodTypeDesc;
import java.util.List;

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
    static void inject(CodeBuilder code, CodegenContext ctx, List<TypeSymbol> bridged, int slot) {
        if (bridged.isEmpty()) {
            code.areturn();
            return;
        }
        code.astore(slot);
        for (TypeSymbol member : bridged) {
            Label next = code.newLabel();
            code.aload(slot);
            code.instanceOf(ctx.caseCarrierClass(member));
            code.ifeq(next);
            ClassDesc bridge = ctx.bridgeCaseClass(member);
            Type held = TypeOps.caseBindType(member);
            code.new_(bridge);
            code.dup();
            code.aload(slot);
            JvmTypes.castFromObject(code, held, ctx);
            code.invokespecial(bridge, "<init>",
                    MethodTypeDesc.of(ConstantDescs.CD_void, JvmTypes.jvmType(held, ctx)));
            code.areturn();
            code.labelBinding(next);
        }
        code.aload(slot);
        code.areturn();
    }

    /**
     * Reads the Souther value out of the union member on the stack, leaving it boxed.
     *
     * <p>Over what the callee's projection says its members reach the union through: a member is
     * local to the union's own module, which for a call is the callee's and not this one's, and
     * which bridge class it arrives in is that module's to say.
     */
    static void project(CodeBuilder code, LinkageProjection.Behavior callee, int slot) {
        List<LinkageProjection.Bridged> bridged = callee.answeredThrough();
        if (bridged.isEmpty()) {
            return;
        }
        code.astore(slot);
        Label done = code.newLabel();
        for (LinkageProjection.Bridged member : bridged) {
            Label next = code.newLabel();
            ClassDesc bridge = member.bridgeClass();
            code.aload(slot);
            code.instanceOf(bridge);
            code.ifeq(next);
            code.aload(slot);
            code.checkcast(bridge);
            code.invokevirtual(bridge, "value", member.valueType());
            JvmTypes.box(code, TypeOps.caseBindType(member.member()));
            code.goto_(done);
            code.labelBinding(next);
        }
        code.aload(slot);
        code.labelBinding(done);
    }
}
