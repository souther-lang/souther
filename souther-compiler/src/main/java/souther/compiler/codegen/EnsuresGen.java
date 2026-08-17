package souther.compiler.codegen;

import souther.compiler.check.BehaviorContract;
import souther.compiler.check.BehaviorContract.ContractParam;
import souther.compiler.check.BehaviorContract.Guard;
import souther.compiler.check.BehaviorContract.Rule;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.Refinement;
import souther.compiler.types.Type;

import java.lang.classfile.ClassFile;
import java.lang.classfile.CodeBuilder;
import java.lang.classfile.Label;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.MethodTypeDesc;
import java.util.ArrayList;
import java.util.List;

import static souther.compiler.codegen.Descriptors.CD_ConstraintViolation;
import static souther.compiler.codegen.Descriptors.CD_EnsuresFailure;
import static souther.compiler.codegen.Descriptors.MTD_ensuresFailure;
import static souther.compiler.codegen.Descriptors.MTD_notHeld;
import static souther.compiler.codegen.Descriptors.build;
import static souther.compiler.codegen.JvmTypes.unbox;

/**
 * The class a behavior's declared relation is checked by.
 *
 * <p>{@code check(Object p0, …, Object pn, Object value)} runs every rule the answer satisfies and
 * aborts at the first that does not hold. Three callers reach it — the behavior's own {@code apply},
 * the crossing an injected answer enters generated code by, and a row validating a fixture — so it
 * is a class of its own with one address they all name the same way.
 *
 * <p>Every argument is a reference. What a behavior may declare is bounded by parameter count and
 * not by width ({@link JvmLimits}), so a behavior taking the largest admissible number of parameters
 * and answering an {@code Int} would push a check that took its answer as a {@code long} past the
 * method's slot limit — a clause added to a legal behavior would stop it being emitted. It also
 * keeps one descriptor for the three callers, so the reflection a row uses does not work out a
 * signature.
 *
 * <p>Every rule whose guard holds is run, and running one does not stop the next. That is what a
 * declaration states: a conjunction, not an ordered choice. A {@code match} takes the first arm that
 * answers because control flow has to go somewhere; a declaration has no order to read, and one
 * answer may satisfy several guards — a data may be a case of two sums its module declares.
 */
final class EnsuresGen {

    private final CodegenContext ctx;

    EnsuresGen(CodegenContext ctx) {
        this.ctx = ctx;
    }

    /** The class carrying {@code contract}'s check. */
    byte[] generate(BehaviorContract contract) {
        ClassDesc cd = ctx.cd(new GeneratedClass.Ensures(
                new GeneratedClass.BehaviorInterface(contract.behavior().module(),
                        contract.behavior().name())));
        List<ClassDesc> params = new ArrayList<>();
        for (int i = 0; i <= contract.params().size(); i++) {
            params.add(ConstantDescs.CD_Object);
        }
        MethodTypeDesc check = MethodTypeDesc.of(ConstantDescs.CD_void,
                params.toArray(new ClassDesc[0]));
        return build(cd, cb -> {
            cb.withFlags(ClassFile.ACC_PUBLIC | ClassFile.ACC_FINAL | ClassFile.ACC_SUPER);
            cb.withMethodBody("check", check, ClassFile.ACC_STATIC | ClassFile.ACC_PUBLIC,
                    code -> emitCheck(code, cd, contract));
        });
    }

    /**
     * The parameters into the slots a rule names them by, then the rules.
     *
     * <p>The answer stays boxed in the slot it arrived in: which case it is, is a question about the
     * carrier, and every rule asks it again. What a rule reads {@code value} as is the case's own,
     * and is put in a slot of its own where that rule needs it.
     */
    private void emitCheck(CodeBuilder code, ClassDesc cd, BehaviorContract contract) {
        // The answer's argument, which is the last one. Held before the parameters take their slots,
        // so nothing below has to work out where it went.
        int answer = contract.params().size();

        BodyGen gen = new BodyGen(ctx, code, null, cd, contract.params().size() + 1);
        for (ContractParam param : contract.params()) {
            code.aload(param.index());
            int slot = gen.slot(param.type());
            unbox(code, param.type(), slot, ctx);
            gen.bind(param.binding(), nameOf(contract, param), slot, param.type());
        }
        for (Rule rule : contract.rules()) {
            emitRule(code, gen, contract, rule, answer);
        }
        code.return_();
    }

    /**
     * One rule: where the answer is this case, what has to hold of it.
     *
     * <p>The guard is a jump past this rule and not a choice between rules — the rule after it is
     * emitted whether or not this one applied, which is what makes the clause a conjunction.
     */
    private void emitRule(CodeBuilder code, BodyGen gen, BehaviorContract contract, Rule rule,
                          int answer) {
        Label next = code.newLabel();
        CaseSelector selector =
                rule.guard() instanceof Guard.Case(CaseSelector named) ? named : null;
        if (selector != null) {
            CaseGen.jumpUnlessMatches(code, ctx, selector, answer, next);
        }
        Type valueType = rule.valueType(contract.output());
        Refinement refinement =
                selector == null ? null : selector.refinement();
        if (refinement instanceof Refinement.OptionAbsent) {
            // The case carries nothing, so there is nothing to bind. A rule about it refers to the
            // answer through its guard, which is what having got here is.
            emitStatement(code, gen, contract, rule, next, selector);
            return;
        }
        if (refinement == null) {
            code.aload(answer);
        } else {
            CaseGen.pushBound(code, refinement, answer);
        }
        int slot = gen.slot(valueType);
        unbox(code, valueType, slot, ctx);
        gen.bind(rule.value(), "value", slot, valueType);
        emitStatement(code, gen, contract, rule, next, selector);
    }

    /** The rule's statement, and the abort where it does not hold. */
    private void emitStatement(CodeBuilder code, BodyGen gen, BehaviorContract contract, Rule rule,
                               Label next, CaseSelector selector) {
        gen.expr(rule.statement());
        code.ifne(next);
        emitAbort(code, contract, rule, selector);
        code.labelBinding(next);
    }

    /** {@code throw ConstraintViolation.notHeld(new EnsuresFailure(…))}. */
    private void emitAbort(CodeBuilder code, BehaviorContract contract, Rule rule,
                           CaseSelector selector) {
        code.new_(CD_EnsuresFailure);
        code.dup();
        code.ldc(contract.behavior().module());
        code.ldc(contract.behavior().name());
        pushOrNull(code, contract.clauseOf(rule).name().orElse(null));
        pushOrNull(code, selector == null ? null : selector.name().name());
        code.invokespecial(CD_EnsuresFailure, ConstantDescs.INIT_NAME, MTD_ensuresFailure);
        code.invokestatic(CD_ConstraintViolation, "notHeld", MTD_notHeld);
        code.athrow();
    }

    private static void pushOrNull(CodeBuilder code, String text) {
        if (text == null) {
            code.aconst_null();
        } else {
            code.ldc(text);
        }
    }

    /** What a parameter is called, which is only ever read by the debugger a local variable table
     *  serves. A rule names it by its binding. */
    private static String nameOf(BehaviorContract contract, ContractParam param) {
        return "in" + param.index();
    }
}
