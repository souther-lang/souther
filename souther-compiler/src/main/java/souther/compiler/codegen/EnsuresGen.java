package souther.compiler.codegen;

import souther.compiler.check.BehaviorContract;
import souther.compiler.check.BehaviorContract.ContractParam;
import souther.compiler.check.BehaviorContract.Guard;
import souther.compiler.check.BehaviorContract.Rule;
import souther.compiler.check.TypeOps;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.Refinement;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.lang.classfile.ClassFile;
import java.lang.classfile.CodeBuilder;
import java.lang.classfile.Label;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.MethodTypeDesc;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static souther.compiler.codegen.Descriptors.CD_ConstraintViolation;
import static souther.compiler.codegen.Descriptors.CD_EnsuresFailure;
import static souther.compiler.codegen.Descriptors.CD_String;
import static souther.compiler.codegen.Descriptors.MTD_ensuresFailure;
import static souther.compiler.codegen.Descriptors.MTD_equalsObject;
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
 * <p>{@code checkCase(Object p0, …, Object pn, String case)} is the same declaration asked of
 * weaker evidence: the case the answer is, where no value was written. An {@code example} row
 * writing a bare case name has stated that much — an arm is a reference to the answer — so the
 * rules that case decides on its own are run and the rest stay undecided. Two entry points and one
 * owner: what a clause means is worked out here for both, and a caller chooses between them by
 * what it has rather than by knowing which rules follow from it.
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
        List<ClassDesc> byCase = new ArrayList<>(params);
        byCase.set(contract.params().size(), CD_String);
        MethodTypeDesc checkCase = MethodTypeDesc.of(ConstantDescs.CD_void,
                byCase.toArray(new ClassDesc[0]));
        return build(cd, cb -> {
            cb.withFlags(ClassFile.ACC_PUBLIC | ClassFile.ACC_FINAL | ClassFile.ACC_SUPER);
            cb.withMethodBody("check", check, ClassFile.ACC_STATIC | ClassFile.ACC_PUBLIC,
                    code -> emitCheck(code, cd, contract));
            cb.withMethodBody("checkCase", checkCase, ClassFile.ACC_STATIC | ClassFile.ACC_PUBLIC,
                    code -> emitCheckByCase(code, cd, contract));
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

        BodyGen gen = bindParams(code, cd, contract);
        // Where the case the answer is, is written before the abort is built. Read off the answer
        // and only where a rule is about to refuse it, so a call that holds pays nothing for it.
        int answered = gen.slot(Type.STRING);
        for (Rule rule : contract.rules()) {
            emitRule(code, gen, contract, rule, answer, answered);
        }
        code.return_();
    }

    /**
     * The parameters into the slots a rule names them by, whichever entry point this is.
     *
     * <p>A rule names a parameter by its binding, and both checks are handed the same parameters in
     * the same argument positions. What follows them differs and this does not.
     */
    private BodyGen bindParams(CodeBuilder code, ClassDesc cd, BehaviorContract contract) {
        BodyGen gen = new BodyGen(ctx, code, null, cd, contract.params().size() + 1);
        for (ContractParam param : contract.params()) {
            code.aload(param.index());
            int slot = gen.slot(param.type());
            unbox(code, param.type(), slot, ctx);
            gen.bind(param.binding(), param.name(), slot, param.type());
        }
        return gen;
    }

    /**
     * The parameters, then the rules the named case decides on its own.
     *
     * <p>A rule is here where its guard is an arm the case satisfies and its statement does not read
     * the answer. Both are settled here, where the declaration is: which cases an arm answers for is
     * a question about the output's declarations, and whether a statement reads {@code value} is a
     * question about the rule ({@link Rule#readsAnswer()}). A caller hands over the case it has and
     * is told what does not hold; it is not asked which rules follow from it.
     *
     * <p>The case arrives as the name it is declared under and is compared as one. An arm may name a
     * sum and a written answer is one of its leaves, so what a rule is guarded by here is the set of
     * leaves its arm answers for — worked out from the declarations rather than tested against a
     * class, since there is no value to test.
     */
    private void emitCheckByCase(CodeBuilder code, ClassDesc cd, BehaviorContract contract) {
        int named = contract.params().size();

        BodyGen gen = bindParams(code, cd, contract);
        // The case that answered, kept for the abort. Written where a leaf is matched rather than
        // worked out again there: which leaf it was is known at the comparison, and asking the
        // argument a second time would be the same question answered twice.
        int answered = gen.slot(Type.STRING);
        for (Rule rule : contract.rules()) {
            if (!(rule.guard() instanceof Guard.Case(CaseSelector selector)) || rule.readsAnswer()) {
                continue;
            }
            Set<TypeSymbol> answersFor = answersFor(selector);
            if (answersFor.isEmpty()) {
                continue;
            }
            Label next = code.newLabel();
            Label matched = code.newLabel();
            for (TypeSymbol leaf : answersFor) {
                // The constant is the receiver, so a case nothing was handed for is a comparison
                // that answers no rather than one that throws.
                code.ldc(leaf.qualified());
                code.aload(named);
                code.invokevirtual(CD_String, "equals", MTD_equalsObject);
                Label notThis = code.newLabel();
                code.ifeq(notThis);
                code.ldc(leaf.name());
                code.astore(answered);
                code.goto_(matched);
                code.labelBinding(notThis);
            }
            code.goto_(next);
            code.labelBinding(matched);
            emitStatement(code, gen, contract, rule, next, selector, () -> code.aload(answered));
        }
        code.return_();
    }

    /**
     * The cases an arm answers for, as the names they are declared under.
     *
     * <p>Its leaves, because that is what a written answer is one of: a union member may be a sum,
     * and an arm naming that sum is about each of the cases it has. Read off the selector, which is
     * what a selector is for — what a case means was settled where the arm was specialized, and
     * working it back out of the name here would be a second answer to it.
     *
     * <p>Empty for a carrier that is not a case a written answer wears: an optional's, which is
     * made by its own factory and named by neither of the two, and a carrier standing under no
     * readable type. A rule guarded by one of those is decided nowhere but at the answer.
     */
    private Set<TypeSymbol> answersFor(CaseSelector selector) {
        return selector.refinement() instanceof Refinement.Direct(Type bound) && bound != null
                ? TypeOps.leafCases(bound, ctx.symbols)
                : Set.of();
    }

    /**
     * One rule: where the answer is this case, what has to hold of it.
     *
     * <p>The guard is a jump past this rule and not a choice between rules — the rule after it is
     * emitted whether or not this one applied, which is what makes the clause a conjunction.
     */
    private void emitRule(CodeBuilder code, BodyGen gen, BehaviorContract contract, Rule rule,
                          int answer, int answered) {
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
            emitStatement(code, gen, contract, rule, next, selector,
                    () -> readAnsweredCase(code, selector, answer, answered));
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
        emitStatement(code, gen, contract, rule, next, selector,
                () -> readAnsweredCase(code, selector, answer, answered));
    }

    /**
     * The rule's statement, and the abort where it does not hold.
     *
     * <p>{@code pushAnswered} leaves the case the answer is on the stack, and is run only here —
     * on the path that refuses. What it costs is paid by a call that was going to abort anyway.
     */
    private void emitStatement(CodeBuilder code, BodyGen gen, BehaviorContract contract, Rule rule,
                               Label next, CaseSelector selector, Runnable pushAnswered) {
        gen.expr(rule.statement());
        code.ifne(next);
        emitAbort(code, contract, rule, selector, pushAnswered);
        code.labelBinding(next);
    }

    /** {@code throw ConstraintViolation.notHeld(new EnsuresFailure(…))}. */
    private void emitAbort(CodeBuilder code, BehaviorContract contract, Rule rule,
                           CaseSelector selector, Runnable pushAnswered) {
        code.new_(CD_EnsuresFailure);
        code.dup();
        code.ldc(contract.behavior().module());
        code.ldc(contract.behavior().name());
        pushOrNull(code, contract.clauseOf(rule).name().orElse(null));
        pushOrNull(code, selector == null ? null : selector.name().name());
        if (selector == null) {
            code.aconst_null();
        } else {
            pushAnswered.run();
        }
        code.invokespecial(CD_EnsuresFailure, ConstantDescs.INIT_NAME, MTD_ensuresFailure);
        code.invokestatic(CD_ConstraintViolation, "notHeld", MTD_notHeld);
        code.athrow();
    }

    /**
     * Writes the case the answer in {@code answer} is into {@code into}, then leaves it on the
     * stack.
     *
     * <p>The leaves of the arm, tested against the value. An arm may name a case that has cases of
     * its own, and what answered is one of those — so a reading that stopped at the arm would name
     * an {@code Errors} for an answer no run produces. Which leaves those are is worked out where
     * this is emitted; the value only says which of them it is.
     *
     * <p>Into a slot before the abort is built rather than onto the stack while it is being built:
     * the tests branch, and a half-made object sitting on the stack across a branch is a shape to
     * keep out of the emitter.
     *
     * <p>The arm's own name is what is left where no leaf answers. A carrier with no leaf a written
     * answer wears — an optional's — has nothing more to say than which carrier it is.
     */
    private void readAnsweredCase(CodeBuilder code, CaseSelector selector, int answer, int into) {
        Label done = code.newLabel();
        for (TypeSymbol leaf : answersFor(selector)) {
            Label notThis = code.newLabel();
            code.aload(answer);
            code.instanceOf(ctx.matchCaseClass(leaf));
            code.ifeq(notThis);
            code.ldc(leaf.name());
            code.astore(into);
            code.goto_(done);
            code.labelBinding(notThis);
        }
        code.ldc(selector.name().name());
        code.astore(into);
        code.labelBinding(done);
        code.aload(into);
    }

    private static void pushOrNull(CodeBuilder code, String text) {
        if (text == null) {
            code.aconst_null();
        } else {
            code.ldc(text);
        }
    }

}
