package souther.compiler.codegen;

import souther.compiler.check.Symbols;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.BehaviorMessage;
import souther.compiler.diag.msg.ModuleMessage;
import souther.compiler.diag.DiagnosticCode;
import souther.compiler.diag.SourcePos;
import souther.compiler.ast.Ast;
import souther.compiler.ast.WrittenName;
import souther.compiler.check.BehaviorRequirement;
import souther.compiler.check.PipelineSigs;
import souther.compiler.check.ReqSig;
import souther.compiler.check.Requirements;
import souther.compiler.check.Sig;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.check.TypeChecker;
import souther.compiler.check.TypeOps;
import souther.compiler.core.Core;

import java.lang.classfile.Annotation;
import java.lang.classfile.ClassBuilder;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassSignature;
import java.lang.classfile.CodeBuilder;
import java.lang.classfile.Label;
import java.lang.classfile.MethodSignature;
import java.lang.classfile.attribute.PermittedSubclassesAttribute;
import java.lang.classfile.attribute.RuntimeInvisibleAnnotationsAttribute;
import java.lang.classfile.attribute.SignatureAttribute;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.MethodTypeDesc;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import static souther.compiler.codegen.Descriptors.*;
import static souther.compiler.codegen.JvmTypes.*;

/**
 * The ClassFile-API backend (spec §jvm-output, §compiler-pipeline). Emits JVM bytecode directly for each
 * {@code data}: the value class (package-private ctor + invariant-checking
 * {@code __construct}) and nested {@code $Dec}/{@code $Enc} classes. Fields may reference
 * other data types; object decoders accumulate every field error (spec §case-propagation).
 */
public final class Backend {

    private final CodegenContext ctx;
    /** Aliases of {@link CodegenContext#pkg}/{@link CodegenContext#symbols}, read as bare names by
     * the code still living here. */
    private final String pkg;
    private final Symbols symbols;

    private final CodecGen codec;
    private final ValueClassGen value;
    /** The checker's elaborated bodies: what this emits from (issue #81). */
    private final TypeChecker.Checked checked;

    /**
     * Every fn {@code module} emits a method for: what its source declared, and what it took on to
     * emit because it reaches a recursive helper it did not write.
     *
     * <p>The two are one question down here and two everywhere above. What may be walked, what must
     * be proven total, what the module publishes — each of those is about the declaring module and
     * reads the component the fn is in; a class being written is about neither, because a method is a
     * method.
     */
    private static List<Ast.FnDef> emitted(Ast.Module module) {
        List<Ast.FnDef> all = new ArrayList<>(module.fns());
        all.addAll(module.takenOn());
        return all;
    }

    private Backend(CodegenContext ctx, TypeChecker.Checked checked) {
        this.ctx = ctx;
        this.pkg = ctx.pkg;
        this.symbols = ctx.symbols;
        this.codec = new CodecGen(ctx);
        this.value = new ValueClassGen(ctx, codec);
        this.checked = checked;
    }

    /** The body the checker elaborated for {@code name}. Codegen runs only on a module that type
     * checked, and the check elaborates every body the backend emits, so a missing one is a compiler
     * invariant violation rather than something to emit around. */
    private static Core elaborated(Map<String, Core> bodies, String name) {
        Core body = bodies.get(name);
        if (body == null) {
            throw new IllegalStateException("no elaborated body for `" + name + "`");
        }
        return body;
    }

    /** {@code ACC_PUBLIC} when the name is exposed (or the module exposes all), else 0. */
    private int pub(String name) {
        return ctx.pub(name);
    }

    /** Generates a module's classes. {@code symbols} covers own plus imported definitions;
     * {@code typePackage} maps an imported type or behavior name to its declaring module (spec §modules);
     * {@code importedSigs} carries imported behaviors' signatures so a composition can name one as a stage
     * (spec §composition); {@code importedInjected} are imported injection-target behaviors, which a
     * composition here inherits as requirements to inject and bind (spec §injected-behavior,
     * §composition-with-requirements); {@code requirements} says what each behavior takes injected and in
     * what order — the answer the example verifier reads too, so a fake reaches the parameter this
     * constructor binds it to; {@code checked} carries the type checker's elaborated bodies, which is what
     * the emitter reads instead of inferring types again (issue #81); {@code dischargeInvariants} carries
     * this module's invariant clauses in the representation the language's own operations survive in, which
     * is what a derived decoder's constraint mapping reads (spec §decoder-error). */
    public static Map<String, byte[]> generate(Ast.Module module, Symbols symbols,
                                               Map<String, String> typePackage,
                                               Map<String, Sig> sigs,
                                               Map<String, Sig> importedSigs,
                                               Set<String> importedInjected,
                                               Map<String, ReqSig> calleeSigs,
                                               Map<String, List<BehaviorRequirement>> requirements,
                                               TypeChecker.Checked checked,
                                               Map<TypeName, List<Ast.InvariantClause>> dischargeInvariants) {
        return generate(module, symbols, typePackage, sigs, importedSigs, importedInjected, calleeSigs,
                requirements, checked, dischargeInvariants, Instrumentation.NONE);
    }

    /**
     * The same classes, counting what the code goes through and recording which arms it took.
     *
     * <p>An overload rather than a mode on the one signature, because these classes are not the
     * module's classes. They call into the compiler, they are never written out, and the only things
     * that ask for them are an evaluation and a measurement. Anything that ships goes through the
     * signature above and gets bytecode with no reference to either in it at all.
     *
     * <p>An {@code instrumentation} carrying a coverage plan must have been made from the bodies in
     * {@code checked} — the same instances, not equal ones. The emitter looks each node up by identity
     * and refuses to emit a body it cannot find an arm for, rather than emit one arm short and report
     * the arm that ran as one nothing reaches.
     */
    public static Map<String, byte[]> generate(Ast.Module module, Symbols symbols,
                                               Map<String, String> typePackage,
                                               Map<String, Sig> sigs,
                                               Map<String, Sig> importedSigs,
                                               Set<String> importedInjected,
                                               Map<String, ReqSig> calleeSigs,
                                               Map<String, List<BehaviorRequirement>> requirements,
                                               TypeChecker.Checked checked,
                                               Map<TypeName, List<Ast.InvariantClause>> dischargeInvariants,
                                               Instrumentation instrumentation) {
        try {
            return generating(module, symbols, typePackage, sigs, importedSigs, importedInjected,
                    calleeSigs, requirements, checked, dischargeInvariants, instrumentation);
        } catch (IllegalArgumentException e) {
            // Something the writer would not hold, from a member no definition here claimed — a
            // synthesised class, a shared one. It belongs to the module, which is as near as anything
            // gets to naming it.
            throw asLimit(e, WrittenName.synthetic(module.name(), module.pos()));
        }
    }

    private static Map<String, byte[]> generating(Ast.Module module, Symbols symbols,
                                                  Map<String, String> typePackage,
                                                  Map<String, Sig> sigs,
                                                  Map<String, Sig> importedSigs,
                                                  Set<String> importedInjected,
                                                  Map<String, ReqSig> calleeSigs,
                                                  Map<String, List<BehaviorRequirement>> requirements,
                                                  TypeChecker.Checked checked,
                                                  Map<TypeName, List<Ast.InvariantClause>> dischargeInvariants,
                                                  Instrumentation instrumentation) {
        Map<String, List<String>> caseToSums = new HashMap<>();
        for (Ast.Def def : module.defs()) {
            if (def instanceof Ast.SumData sum) {
                for (Ast.Name caseName : sum.cases()) {
                    caseToSums.computeIfAbsent(caseName.denotes().name(), k -> new ArrayList<>())
                            .add(sum.name());
                }
            }
        }
        // The checker has already run and rejects any dotted `A.decoder`/`.encoder` member
        // (exposing is type-granular, spec §jvm-codec), so every entry that reaches codegen is a bare name.
        Set<String> exposed = new HashSet<>(module.exposing());
        // After the Lower stage the only non-behavior fns left are recursive helpers (spec §fn-declaration);
        // each is lowered to a static method on the module's `$Fns` class rather than inlined.
        Set<String> behaviorNames = new HashSet<>();
        for (Ast.BehaviorDef bd : module.behaviors()) {
            behaviorNames.add(bd.name());
        }
        // Both components: a method is emitted for what the module declared and for what it took on
        // to emit, and by the time a class is written there is no difference between them.
        Map<String, Ast.FnDef> recHelpers = new LinkedHashMap<>();
        for (Ast.FnDef fn : emitted(module)) {
            if (!behaviorNames.contains(fn.name())) {
                recHelpers.put(fn.name(), fn);
            }
        }
        CodegenContext ctx = new CodegenContext(module.name(), symbols, caseToSums, typePackage,
                module.exposing().isEmpty(), exposed, recHelpers);
        ctx.setDischargeInvariants(dischargeInvariants);
        ctx.setCoveragePlan(instrumentation.coverage());
        ctx.setCounting(instrumentation.counting());
        Backend b = new Backend(ctx, checked);
        // Before anything is written: a declaration wide enough that its generated method cannot hold
        // its arguments produces a class the JVM refuses at load time, and nothing downstream notices.
        JvmLimits.checkParameterSlots(module, ctx, recHelpers, sigs, requirements);
        // A behavior's class capitalizes its first letter (spec §jvm-behavior). Data names are already
        // capitalized, so `behavior quote` producing `data Quote` would generate two classes named
        // `Quote`. Reject the collision here rather than let one silently overwrite the other.
        Set<String> localTypes = new HashSet<>();
        for (Ast.Def d : module.defs()) {
            localTypes.add(d.name());
        }
        Map<String, String> behaviorClassOwner = new HashMap<>();
        for (Ast.BehaviorDef bd : module.behaviors()) {
            String cls = behaviorClass(bd.name());
            if (localTypes.contains(cls)) {
                throw CompileException.of(Diagnostic
                                .at(bd.pos()).say(new BehaviorMessage.ABehaviorCapitalizesOntoAData(bd.name(), cls)).build());
            }
            String prev = behaviorClassOwner.put(cls, bd.name());
            if (prev != null) {
                throw CompileException.of(Diagnostic
                                .at(bd.pos()).say(new BehaviorMessage.TwoBehaviorsCapitalizeToOneClass(prev, bd.name(), cls)).build());
            }
        }
        // A behavior whose output is an anonymous union gets a generated sealed interface
        // <behavior名>Result that its cases implement (spec §jvm-anonymous-union). Register those case->interface links
        // in caseToSums before the data classes are generated, so each case class picks the interface
        // up in withInterfaceSymbols. The interface classes themselves are emitted below.
        Map<String, List<TypeName>> behaviorResults = b.behaviorResultInterfaces(module, sigs);
        b.rejectResultUnionCollisions(module, behaviorResults, localTypes, behaviorClassOwner);
        // A case class carries the result unions it belongs to as interfaces it implements, and that
        // list is settled when its own module is generated. A member this module declared takes the
        // interface on itself. A primitive and a type another module emitted cannot: `java.lang.Long`
        // is the JDK's, and giving an imported class an interface from here would make a module's
        // bytecode depend on which modules import it — the mirror of what ADR-0024 refuses. Such a
        // member reaches the union through a bridge case this module emits instead (ADR-0057).
        Map<TypeName, List<String>> bridgeCases = new LinkedHashMap<>();
        behaviorResults.forEach((resultName, members) -> {
            for (TypeName member : members) {
                if (b.ctx.isLocalMember(member)) {
                    caseToSums.computeIfAbsent(member.name(), k -> new ArrayList<>()).add(resultName);
                } else {
                    bridgeCases.computeIfAbsent(member, k -> new ArrayList<>()).add(resultName);
                }
            }
        });
        b.rejectBridgeCaseCollisions(module, bridgeCases, behaviorResults, localTypes, behaviorClassOwner);
        Map<String, byte[]> out = new OneClassPerName();
        behaviorResults.forEach((resultName, members) -> {
            // the union and its encoder belong to the behavior whose output they are, not to the
            // module, though the behavior did not write them
            Ast.BehaviorDef owner = b.behaviorOf(module, resultName);
            // A module's own name is the one name the tree does not carry an occurrence for, so
            // where a result belongs to no behavior the report is anchored at the module and is as
            // wide as its name rather than as the characters that spell it.
            emitting(owner == null
                    ? WrittenName.synthetic(module.name(), module.pos()) : owner.written(), () -> {
                        out.put(module.name() + "." + resultName,
                                b.generateBehaviorResult(resultName, members));
                        out.put(module.name() + "." + resultName + "$Enc",
                                b.codec.generateResultUnionEncoder(resultName, members));
                    });
        });
        // A bridge case is shared by every union that reaches its member, so no one behavior owns it;
        // it is left to the module, which the outermost boundary answers for.
        bridgeCases.forEach((member, unions) ->
                out.put(module.name() + "." + CodegenContext.bridgeCaseName(member),
                        b.value.generateBridgeCase(member, unions, out)));
        for (Ast.Def def : module.defs()) {
            emitting(def.written(), () -> {
                switch (def) {
                    case Ast.Data data -> b.value.generateData(data, out);
                    case Ast.SumData sum -> b.value.generateSum(sum, out);
                    case Ast.UnitData unit -> b.value.generateUnit(unit, out);
                }
            });
        }
        // Behavior fn bodies arrive with their helper calls already inlined (the Lower stage,
        // ADR-0021); the backend emits them as-is and never lowers a helper on its own.
        Map<String, Ast.FnDef> fns = new HashMap<>();
        for (Ast.FnDef fn : emitted(module)) {
            fns.put(fn.name(), fn);
        }
        // Injection targets (spec §injected-behavior): a SpecBehavior with no matching fn. Each becomes an
        // abstract base class a Java implementation extends (§java-base-class). Imported injection targets
        // (their base lives in the declaring module) are requirements too, so a composition here
        // injects and binds them (spec §composition-with-requirements) — but no base is generated for them here.
        Set<String> requiredNames = Requirements.injectedNames(module, importedInjected);
        Map<String, Type> requiredSuccess = new HashMap<>();
        Map<String, List<Type>> requiredParam = new HashMap<>();
        for (Ast.BehaviorDef bd : module.behaviors()) {
            if (bd instanceof Ast.SpecBehavior spec && requiredNames.contains(spec.name())) {
                requiredSuccess.put(spec.name(), b.successType(spec.ret()));
                List<Type> reqParams = new ArrayList<>();
                for (Ast.Param p : spec.params()) {
                    reqParams.add(b.successType(p.type()));
                }
                requiredParam.put(spec.name(), reqParams);
                // Unit output cases get a no-arg factory (a unit has nothing to validate, so it is
                // built directly). A field-bearing constructed type gets a typed factory, but only
                // when the behavior declares it in `constructs` — that declaration is the authority
                // to build it (spec §asymmetric-interop), and unlike a unit it cannot be told apart from a decoded
                // pass-through output (会員) by shape alone.
                List<String> unitCases = new ArrayList<>();
                for (Ast.TypeTerm term : spec.ret().cases()) {
                    if (term instanceof Ast.TypeRef t && t.denotes() instanceof Type.Ref r
                            && b.symbols.get(r.name()) instanceof Ast.UnitData) {
                        unitCases.add(r.name().name());
                    }
                }
                List<Ast.Data> dataConstructs = new ArrayList<>();
                Set<TypeName> seenConstruct = new HashSet<>();
                if (spec.constructs() != null) {
                    for (Ast.Name tn : spec.constructs()) {
                        // a field-bearing data or newtype; de-duplicated so a repeated `constructs`
                        // entry does not emit the factory method twice (a duplicate-method class file)
                        if (b.symbols.get(tn.denotes()) instanceof Ast.Data data
                                && seenConstruct.add(tn.denotes())) {
                            dataConstructs.add(data);
                        }
                    }
                }
                emitting(spec.written(), () ->
                        out.put(module.name() + "." + behaviorClass(spec.name()),
                                b.generateRequiredBase(spec.name(), unitCases, dataConstructs,
                                        reqParams, b.successType(spec.ret()))));
            }
        }
        // An imported injected behavior (its base lives in the declaring module, so no base is built
        // here) is a requirement too; take its arity from the imported signature so the unary-vs-multi
        // dispatch treats a cross-module multi-input dependency the same as a local one (issue #57).
        // A behavior with an implementation of its own may be a requirement too, when it declares
        // `depends on` (spec [#depends-on]). Nothing is generated for it here — it has its own $Impl —
        // but the module that named it holds it as a field, so its arity and output belong in the
        // same maps the unary-vs-multi dispatch reads.
        Map<String, Ast.SpecBehavior> ownSpecs = new HashMap<>();
        for (Ast.BehaviorDef bd : module.behaviors()) {
            if (bd instanceof Ast.SpecBehavior spec) {
                ownSpecs.put(spec.name(), spec);
            }
        }
        for (Ast.BehaviorDef bd : module.behaviors()) {
            if (!(bd instanceof Ast.SpecBehavior spec)) {
                continue;
            }
            for (Ast.Var req : spec.dependsOn()) {
                String name = req.bare();
                if (requiredNames.contains(name)) {
                    continue;
                }
                Ast.SpecBehavior own = ownSpecs.get(name);
                if (own != null) {
                    List<Type> ins = new ArrayList<>();
                    for (Ast.Param p : own.params()) {
                        ins.add(b.successType(p.type()));
                    }
                    requiredNames.add(name);
                    requiredParam.put(name, ins);
                    requiredSuccess.put(name, b.successType(own.ret()));
                    continue;
                }
                Sig imported = importedSigs.get(name);
                if (imported != null) {
                    requiredNames.add(name);
                    requiredParam.put(name, imported.inputTypes());
                    requiredSuccess.put(name, imported.outputType());
                }
            }
        }
        for (String name : importedInjected) {
            Sig sig = importedSigs.get(name);
            if (sig != null) {
                requiredParam.put(name, sig.inputTypes());
                requiredSuccess.put(name, sig.outputType());
            }
        }
        // The unary-vs-multi dispatch for required behaviors reads these; set once, so the base class,
        // the $Impl field/ctor, the bind factory, and every call site agree (issue #57).
        b.ctx.setRequiredSignatures(requiredParam, requiredSuccess);
        // A behavior that depends on nothing is called by being built where it is called, so it is not
        // in the injection maps above; what a call site needs is the signature it was typed against.
        b.ctx.setCalleeSignatures(calleeSigs);
        // What each behavior takes injected, worked out once and read here and at an example
        // (Bodies.Requirements): the order is this constructor's parameter order.
        Map<String, List<String>> behaviorDeps = new LinkedHashMap<>();
        for (Map.Entry<String, List<BehaviorRequirement>> e : requirements.entrySet()) {
            behaviorDeps.put(e.getKey(), Requirements.names(e.getValue()));
        }
        Map<String, List<Ast.Var>> pipeStages = PipelineSigs.pipelineStages(module);
        for (Ast.BehaviorDef bd : module.behaviors()) {
            emitting(bd.written(), () -> {
                switch (bd) {
                    case Ast.SpecBehavior spec -> {
                        Ast.FnDef fn = fns.get(spec.name());
                        if (fn != null) {
                            // a fn-implemented behavior: the $Impl holds the logic, the public interface
                            // (behaviorClass) is what Java code declares (spec §jvm-anonymous-union).
                            out.put(module.name() + "." + CodegenContext.behaviorImplClass(spec.name()),
                                    b.generateSpecFn(spec, fn, requiredNames, requiredSuccess, requiredParam));
                            List<Type> pts = new ArrayList<>();
                            for (Ast.Param p : spec.params()) {
                                pts.add(b.successType(p.type()));
                            }
                            out.put(module.name() + "." + behaviorClass(spec.name()),
                                    b.generateBehaviorInterface(spec.name(), pts, b.successType(spec.ret()),
                                            requiredBy(spec)));
                        }
                        // else: injection target — its abstract base was generated above (spec §java-base-class)
                    }
                    case Ast.PipeBehavior pipe -> {
                        out.put(module.name() + "." + CodegenContext.behaviorImplClass(pipe.name()),
                                b.generatePipe(pipe, requiredNames, sigs, behaviorDeps, pipeStages));
                        Sig sig = declaredSig(pipe, sigs);
                        out.put(module.name() + "." + behaviorClass(pipe.name()),
                                b.generateBehaviorInterface(pipe.name(), sig.inputTypes(), sig.outputType(),
                                        behaviorDeps.getOrDefault(pipe.name(), List.of())));
                    }
                }
            });
        }
        if (!recHelpers.isEmpty()) {
            // The helpers share one class, so the writer names a method rather than a definition: a
            // method it would not write is the helper whose name it is, and a pool it would not hold
            // belongs to all of them and so to the module.
            try {
                out.put(module.name() + ".$Fns", b.generateRecursiveHelpers(recHelpers));
            } catch (IllegalArgumentException e) {
                JvmLimits.Exceeded exceeded = JvmLimits.exceeded(e);
                Ast.FnDef helper = exceeded == null ? null : helperNamed(recHelpers, exceeded.method());
                throw helper == null
                        ? asLimit(e, WrittenName.synthetic(module.name(), module.pos()))
                        : asLimit(e, helper.written());
            }
        }
        out.putAll(b.ctx.synthClasses());   // escaping lambdas compiled to Fn classes (spec §blocks)
        // Every site the plan numbered has to be in the bytecode. A missing arm comes back as an arm
        // no row goes through and a missing comparison as a line no row reached, and both read as the
        // model being short of rows rather than the measurement being short of probes. A body the
        // emitter walks without counting is how that happens, and it is silent at the site — so it is
        // caught here, where the plan and what was emitted can be compared.
        List<Integer> missed = b.ctx.plannedButNotEmitted();
        if (!missed.isEmpty()) {
            throw new IllegalStateException("the plan numbered " + missed.size()
                    + " site(s) that nothing emitted: " + missed
                    + "; a body was walked without counting what it holds");
        }
        return out;
    }

    /**
     * What a module emits, holding one class under one binary name.
     *
     * <p>The names a module declares and the names the compiler generates beside them are spelled
     * into one namespace, and a map takes the second write of a name as the value of it — so two
     * classes wanting one name left the artifact set short of a class, with the compile reporting
     * nothing and the loss arriving as a linkage error against whichever class went missing. The
     * language keeps the two apart by refusing {@code $} in a name (spec §identifier), and a
     * declaration that would emit a class another declaration already has is refused where it is
     * declared (spec §no-two-declarations-become-one-class). This says the same thing at the one
     * place both are true of, so a naming scheme changed later cannot bring the silence back.
     */
    static final class OneClassPerName extends LinkedHashMap<String, byte[]> {

        @Override
        public byte[] put(String name, byte[] bytes) {
            if (containsKey(name)) {
                throw new IllegalStateException("two classes were emitted as " + name
                        + "; a module's declared and generated names are one namespace and this one"
                        + " is written twice");
            }
            return super.put(name, bytes);
        }

        @Override
        public void putAll(Map<? extends String, ? extends byte[]> classes) {
            classes.forEach(this::put);
        }
    }

    /**
     * Emits one definition, saying what the class file writer would not hold as that definition.
     *
     * <p>How long a method is and how many constants a class refers to are not known before it is
     * written, so unlike an argument count they cannot be checked at the declaration. What the writer
     * says names its own rule and the method it was writing, and the author has no way back from
     * either to what they wrote — so it is said here, where the definition being emitted is in hand.
     * A refusal that names no limit is not this compiler's to answer for and goes on unchanged.
     */
    private static void emitting(WrittenName written, Runnable emit) {
        try {
            emit.run();
        } catch (IllegalArgumentException e) {
            throw asLimit(e, written);
        }
    }

    /** The refusal as the diagnostic for {@code name}, or unchanged where it names no limit this
     *  compiler answers for. */
    private static RuntimeException asLimit(IllegalArgumentException e, WrittenName written) {
        JvmLimits.Exceeded exceeded = JvmLimits.exceeded(e);
        return exceeded == null ? e : JvmLimits.tooLarge(exceeded, written);
    }

    /** The helper emitted as {@code method} on {@code $Fns}, or null if the name is not one of
     *  theirs. */
    private static Ast.FnDef helperNamed(Map<String, Ast.FnDef> helpers, String method) {
        if (method == null) {
            return null;
        }
        for (Ast.FnDef helper : helpers.values()) {
            if (CodegenContext.helperMethod(helper.name()).equals(method)) {
                return helper;
            }
        }
        return null;
    }

    /** The {@code $Fns} method a helper is emitted as, for a caller outside this package: an
     * {@code example} that applies a helper looks the method up by name (ADR-0077), and the name is
     * decided in one place. */
    public static String helperMethod(String helper) {
        return CodegenContext.helperMethod(helper);
    }

    /** The {@code $Ctfe} method checking the clause declared {@code i}th, for a caller outside this
     * package: the compile-time check of a constant construction asks one clause at a time, so that a
     * constant the compiler rejects names the rule it broke. */
    public static String clauseCheck(int index) {
        return ValueClassGen.ctfeClauseCheck(index);
    }

    /**
     * Emits the module's recursive helpers as {@code static} methods on a package-private {@code $Fns}
     * class (spec §fn-declaration). Each helper's declared parameter and return types are boxed as {@code Object}
     * across the method boundary, unboxed on entry and boxed on return, so a self- or mutual call is a
     * plain {@code invokestatic} — the recursion the inliner cannot express. The body is emitted through
     * the same {@code emitBodyTail} path a behavior uses; a helper is pure, so it has no injected fields.
     */
    private byte[] generateRecursiveHelpers(Map<String, Ast.FnDef> helpers) {
        ClassDesc cdFns = ClassDesc.of(pkg + ".$Fns");
        return build(cdFns, cb -> {
            cb.withFlags(ClassFile.ACC_FINAL | ClassFile.ACC_SUPER);   // package-private, not exposed
            for (Ast.FnDef h : helpers.values()) {
                int n = h.params().size();
                ClassDesc[] params = new ClassDesc[n];
                java.util.Arrays.fill(params, CD_Object);
                MethodTypeDesc desc = MethodTypeDesc.of(CD_Object, params);
                String called = CodegenContext.helperMethod(h.name());
                // Where the depth is counted, what every caller reaches is the counting wrapper and the
                // body moves aside. A recursive call is an `invokestatic` of the called name (a tail
                // call to the same helper loops instead and adds no frame), so putting the counting
                // there is what makes a recursion count itself however it is reached — from a row, from
                // a fixture's helper, or from another helper in its group.
                String emitted = ctx.counting() ? called + "$body" : called;
                if (ctx.counting()) {
                    cb.withMethodBody(called, desc, ClassFile.ACC_STATIC,
                            code -> emitDepthCounted(code, cdFns, emitted, desc, n));
                }
                cb.withMethodBody(emitted, desc, ClassFile.ACC_STATIC,
                        code -> {
                    BodyGen gen = new BodyGen(ctx, code, null, cdFns, n);
                    for (int i = 0; i < n; i++) {
                        // a function parameter arrives as an Fn value (a closure); every other parameter
                        // as its boxed value. resolveParamType handles both shapes.
                        Type pt = TypeOps.resolveParamType(h.params().get(i).type(), symbols);
                        code.aload(i);
                        int slot = gen.slot(pt);
                        unbox(code, pt, slot);
                        gen.bind(h.params().get(i).binder(), slot, pt);
                    }
                    // A tail-position call to this same helper loops back here instead of recursing,
                    // so a self-tail-recursive helper runs in constant stack.
                    gen.beginSelfRecursion(h.name(), h.params());
                    // a recursive helper declares its return type; thread it so a tail-position fold
                    // over an empty seed materialises its step at the declared type, not a bottom (#70)
                    Type helperReturn = h.declaredReturn() == null ? null : successType(h.declaredReturn());
                    gen.emitTail(elaborated(checked.emittedHelpers(), h.name()),
                            cdFns, Set.of(), Map.of(), helperReturn);
                });
            }
        });
    }

    /**
     * The helper as its callers reach it while an evaluation is counting: one frame counted in, the
     * body applied, and the frame counted out however the body leaves.
     *
     * <p>A wrapper rather than counting inside the body, because leaving has to be counted on every
     * path out and the body has many — every arm of every {@code match} returns on its own. One
     * catch-all handler around one call says the same thing once, and says it for the exceptional path
     * as well, which is the path that matters: a row is given up on by an exception thrown from inside
     * the code, so the depth of a helper it was inside has to come back down as that leaves.
     *
     * <p>Counting the depth is not the same as counting the steps, and neither stands in for the
     * other. A recursion that goes deep in few steps is stopped by this before the stack it runs on
     * runs out, which is what stops how deep it may go from being an answer the JVM gives.
     */
    private static void emitDepthCounted(CodeBuilder code, ClassDesc owner, String body,
                                         MethodTypeDesc desc, int arity) {
        Label from = code.newLabel();
        Label to = code.newLabel();
        Label unwinding = code.newLabel();
        code.invokestatic(CD_EvaluationContext, "enter", MTD_EvaluationContext_count);
        code.labelBinding(from);
        for (int i = 0; i < arity; i++) {
            code.aload(i);
        }
        code.invokestatic(owner, body, desc);
        code.labelBinding(to);
        code.invokestatic(CD_EvaluationContext, "leave", MTD_EvaluationContext_count);
        code.areturn();
        code.exceptionCatchAll(from, to, unwinding);
        code.labelBinding(unwinding);
        code.astore(arity);
        code.invokestatic(CD_EvaluationContext, "leave", MTD_EvaluationContext_count);
        code.aload(arity);
        code.athrow();
    }

    /** Emits injected required-behavior fields plus the matching constructor (or a no-arg ctor) on a
     * behavior's {@code $Impl}. The {@code of()}/{@code bind()} factories live on the public interface
     * ({@link #emitBehaviorFactory}), not here. */
    private void emitInjection(ClassBuilder cb, ClassDesc cdX, List<String> requireds) {
        if (requireds.isEmpty()) {
            emitPublicCtor(cb);
            return;
        }
        for (String req : requireds) {
            // a multi-input required behavior is stored as its own base class (invokevirtual), not the
            // unary Behavior — see CodegenContext.requiredFieldType (issue #57)
            cb.withField(req, ctx.requiredFieldType(req), ClassFile.ACC_FINAL);
        }
        ClassDesc[] params = new ClassDesc[requireds.size()];
        for (int i = 0; i < requireds.size(); i++) {
            params[i] = ctx.requiredFieldType(requireds.get(i));
        }
        MethodTypeDesc ctorDesc = MethodTypeDesc.of(ConstantDescs.CD_void, params);
        cb.withMethodBody("<init>", ctorDesc, ClassFile.ACC_PUBLIC, code -> {
            code.aload(0);
            code.invokespecial(CD_Object, "<init>", MTD_void);
            for (int i = 0; i < requireds.size(); i++) {
                code.aload(0);
                code.aload(i + 1);
                code.putfield(cdX, requireds.get(i), ctx.requiredFieldType(requireds.get(i)));
            }
            code.return_();
        });
    }

    /**
     * Emits the static factory a Java caller uses to build a fn/pipe behavior, on its public
     * interface (spec §jvm-behavior). {@code of()} for a behavior with no {@code depends on}; {@code bind(<named
     * required interfaces>)} for one that injects dependencies. Both return the interface type and
     * construct the {@code $Impl}, so the caller never names the implementation class.
     */
    private void emitBehaviorFactory(ClassBuilder cb, ClassDesc cdI, ClassDesc cdImpl,
                                     List<String> requireds) {
        if (requireds.isEmpty()) {
            cb.withMethodBody("of", MethodTypeDesc.of(cdI),
                    ClassFile.ACC_PUBLIC | ClassFile.ACC_STATIC, code -> {
                        code.new_(cdImpl);
                        code.dup();
                        code.invokespecial(cdImpl, "<init>", MTD_void);
                        code.areturn();
                    });
            return;
        }
        ClassDesc[] bindParams = new ClassDesc[requireds.size()];
        ClassDesc[] ctorParams = new ClassDesc[requireds.size()];
        for (int i = 0; i < requireds.size(); i++) {
            bindParams[i] = cdBehavior(requireds.get(i));   // the required's public interface / base
            ctorParams[i] = ctx.requiredFieldType(requireds.get(i));
        }
        MethodTypeDesc ctorDesc = MethodTypeDesc.of(ConstantDescs.CD_void, ctorParams);
        cb.withMethodBody("bind", MethodTypeDesc.of(cdI, bindParams),
                ClassFile.ACC_PUBLIC | ClassFile.ACC_STATIC, code -> {
                    code.new_(cdImpl);
                    code.dup();
                    for (int i = 0; i < requireds.size(); i++) {
                        code.aload(i);
                    }
                    code.invokespecial(cdImpl, "<init>", ctorDesc);
                    code.areturn();
                });
    }

    /**
     * Generates the abstract base class for a required behavior (spec §java-base-class): an abstract
     * {@code Behavior} that a Java implementation extends. The base exposes a {@code protected}
     * factory for what the implementation may build (spec §closed-construction). The two kinds are sourced differently.
     * A unit output case gets a no-arg factory: a unit has no invariant to validate, so it is built
     * directly, and it is taken from the output cases (an injected behavior may leave {@code constructs}
     * implicit, and a unit is safe to hand out either way). A field-bearing type gets a typed factory
     * built through its {@code __construct} so the invariant is checked, but only when the behavior
     * declares it in {@code constructs}: that declaration is the authority to build it (spec §asymmetric-interop), and
     * unlike a unit it cannot be told apart from a decoded pass-through output by shape alone. The typed
     * factory lets the implementation compose already-held values into its declared output without
     * round-tripping through the decoder. The data constructors stay non-public, so a subclass builds
     * exactly these and nothing else, from any package.
     *
     * <p>When both the input and output map to a concrete reference type, the base carries a generic {@code
     * Behavior<In, Out>} signature (spec §jvm-anonymous-union, §jvm-behavior) — {@code Out} is the {@code
     * <名>Result} interface for an anonymous union output — so a Java author writes the real return type
     * rather than {@code Object}. If either side is a list/option/map (no single reference class), the
     * signature is omitted and the raw interface stands.
     */
    private byte[] generateRequiredBase(String name, List<String> unitCases, List<Ast.Data> dataConstructs,
                                        List<Type> paramTypes, Type retType) {
        ClassDesc cdR = cdBehavior(name);
        // Injected-vs-unary is orthogonal to composition: one input is the unary Behavior<In,Out> (so
        // it can follow an arrow); any other count is a standalone abstract class with a typed
        // apply(A,B,...) — a first stage but never a later one — the same param-count branch a fn
        // behavior takes in generateBehaviorInterface. A `() -> R` produces rather than transforms:
        // there is no input to hand it, so it declares `apply()` instead of taking a value it ignores.
        boolean single = paramTypes.size() == 1;
        return build(cdR, cb -> {
            cb.withFlags(ClassFile.ACC_PUBLIC | ClassFile.ACC_ABSTRACT | ClassFile.ACC_SUPER);
            if (single) {
                withBehaviorSignature(cb, paramTypes.get(0), retType, name);
                cb.withInterfaceSymbols(CD_Behavior);
            } else {
                emitAbstractApply(cb, name, paramTypes, retType);
            }
            // protected no-arg ctor so subclasses in any package can call super()
            cb.withMethodBody("<init>", MTD_void, ClassFile.ACC_PROTECTED, code -> {
                code.aload(0);
                code.invokespecial(CD_Object, "<init>", MTD_void);
                code.return_();
            });
            for (String caseName : unitCases) {
                emitUnitFactory(cb, caseName);
            }
            for (Ast.Data data : dataConstructs) {   // a field-bearing data or a newtype
                emitDataFactory(cb, data);
            }
        });
    }

    /** A no-arg factory for a unit case: the type has exactly one value, so it hands that out. */
    private void emitUnitFactory(ClassBuilder cb, String typeName) {
        ClassDesc caseCd = cd(typeName);
        cb.withMethodBody(typeName, MethodTypeDesc.of(caseCd),
                ClassFile.ACC_PROTECTED | ClassFile.ACC_FINAL, code -> {
                    loadSharedInstance(code, caseCd);
                    code.areturn();
                });
    }

    /** A factory taking the data's fields (in declaration order) and building it through
     * {@code __construct}, so the invariant is checked and a violation aborts (spec §algebraic-types) — the same
     * path an in-domain construction takes, not a decode of an external representation. */
    private void emitDataFactory(ClassBuilder cb, Ast.Data data) {
        ClassDesc cdType = cd(data.name());
        Map<String, Type> fields = ctx.fieldTypes(data);
        ClassDesc[] fieldDs = fieldDescs(fields, ctx);
        String sig = factorySignature(fields, cdType);
        cb.withMethod(data.name(), MethodTypeDesc.of(cdType, fieldDs),
                ClassFile.ACC_PROTECTED | ClassFile.ACC_FINAL, mb -> {
                    if (sig != null) mb.with(SignatureAttribute.of(MethodSignature.parseFrom(sig)));
                    mb.withCode(code -> {
                        int slot = 1;   // slot 0 is `this`
                        for (Type t : fields.values()) {
                            load(code, slot, t);
                            slot += width(t);
                        }
                        code.invokestatic(cdType, "__construct", MethodTypeDesc.of(CD_Result, fieldDs));
                        code.invokestatic(CD_ConstraintViolation, "orThrow", MTD_orThrow);
                        code.checkcast(cdType);
                        code.areturn();
                    });
                });
    }

    /** A generic method {@code Signature} for a factory whose fields include a container
     * (List/Set/Map/Option), else {@code null}. Mirrors the value-class accessor signature (spec §field-visibility)
     * so a Java caller passes {@code List<Line>} rather than a raw {@code List}. A non-container field
     * keeps its plain descriptor; the signature erases to the method's descriptor either way. */
    private String factorySignature(Map<String, Type> fields, ClassDesc ret) {
        boolean anyContainer = false;
        StringBuilder sb = new StringBuilder("(");
        for (Type t : fields.values()) {
            String g = JvmTypes.genericSig(t, ctx);
            if (g != null) {
                anyContainer = true;
                sb.append(g);
            } else {
                sb.append(jvmType(t, ctx).descriptorString());
            }
        }
        sb.append(")").append(ret.descriptorString());
        return anyContainer ? sb.toString() : null;
    }

    /**
     * Adds the source-level {@code Behavior<I, O>} signature to a generated single-input
     * behavior. Its erased JVM {@code apply} descriptor remains {@code Object -> Object}, but
     * Java callers then receive the declared input and outcome types without a cast.
     */
    private void withBehaviorSignature(ClassBuilder cb, Type input, Type output, String behaviorName) {
        // A collection In/Out keeps its element type (sigRefOrNull), so it no longer suppresses the
        // whole Behavior<In,Out> signature — only a truly erased type (var/tuple/fn) does (issue #57).
        String inSig = ctx.sigRefOrNull(input, behaviorName);
        String outSig = ctx.sigRefOrNull(output, behaviorName);
        if (inSig == null || outSig == null) {
            return;
        }
        String beh = CD_Behavior.descriptorString();
        beh = beh.substring(0, beh.length() - 1); // drop trailing ';' to insert type args
        String sig = CD_Object.descriptorString() + beh + "<" + inSig + outSig + ">;";
        cb.with(SignatureAttribute.of(ClassSignature.parseFrom(sig)));
    }

    /** Declares the abstract, typed multi-argument {@code apply(A,B,…)} of a multi-input behavior
     * (a fn interface or an injected base), with a generic {@code Signature} when a param/return is a
     * collection (issue #57). */
    private void emitAbstractApply(ClassBuilder cb, String name, List<Type> paramTypes, Type retType) {
        String sig = ctx.applySignatureOrNull(name, paramTypes, retType);
        cb.withMethod("apply", ctx.typedApplyDesc(name, paramTypes, retType),
                ClassFile.ACC_PUBLIC | ClassFile.ACC_ABSTRACT, mb -> {
                    if (sig != null) {
                        mb.with(SignatureAttribute.of(MethodSignature.parseFrom(sig)));
                    }
                });
    }

    /**
     * The public interface a Java caller declares for a fn/pipe behavior (spec §jvm-anonymous-union). It hides the
     * generated {@code <名>Result} union: the caller writes the behavior name and switches over the
     * cases. A single-input behavior's interface {@code extends Behavior<In, Out>} — so it composes
     * with {@code >->} and its {@code apply} return type is typed by inheritance; a multi-input one is
     * a standalone functional interface declaring a typed, multi-argument {@code apply}. Both carry the
     * static {@code of()}/{@code bind(...)} factory that builds the {@code $Impl}.
     */
    private byte[] generateBehaviorInterface(String name, List<Type> paramTypes, Type retType,
                                             List<String> dependsOn) {
        ClassDesc cdI = cdBehavior(name);
        ClassDesc cdImpl = cdBehaviorImpl(name);
        boolean single = paramTypes.size() == 1;
        return build(cdI, cb -> {
            cb.withFlags(pub(name) | ClassFile.ACC_INTERFACE | ClassFile.ACC_ABSTRACT);
            if (single) {
                cb.withInterfaceSymbols(CD_Behavior);   // extends Behavior<In, Out> (raw if untyped)
                withBehaviorSignature(cb, paramTypes.getFirst(), retType, name);
            } else {
                // no Behavior supertype (it takes one argument): declare the typed apply directly
                emitAbstractApply(cb, name, paramTypes, retType);
            }
            emitBehaviorFactory(cb, cdI, cdImpl, dependsOn);
        });
    }

    private MethodTypeDesc typedApplyDesc(String name, List<Type> paramTypes, Type retType) {
        return ctx.typedApplyDesc(name, paramTypes, retType);
    }

    /** Emits the covariant bridge that satisfies a multi-input interface's typed apply by delegating
     * to the erased {@code apply(Object...)Object} the body lives on. Skipped when the typed and
     * erased descriptors coincide (every param and the return degraded to {@code Object}), because
     * then the erased apply already implements the interface method. */
    private void emitTypedApplyBridge(ClassBuilder cb, ClassDesc cdImpl, MethodTypeDesc typed) {
        int n = typed.parameterCount();
        ClassDesc[] erasedParams = new ClassDesc[n];
        java.util.Arrays.fill(erasedParams, CD_Object);
        MethodTypeDesc erased = MethodTypeDesc.of(CD_Object, erasedParams);
        if (typed.equals(erased)) {
            return;
        }
        cb.withMethodBody("apply", typed, ClassFile.ACC_PUBLIC, code -> {
            code.aload(0);
            for (int i = 0; i < n; i++) {
                code.aload(i + 1);
            }
            code.invokevirtual(cdImpl, "apply", erased);
            ClassDesc ret = typed.returnType();
            if (!ret.equals(CD_Object)) {
                code.checkcast(ret);
            }
            code.areturn();
        });
    }

    /**
     * Behavior-result interfaces to generate (spec §jvm-anonymous-union): for each behavior whose output is an
     * anonymous union, maps {@code <behavior名>Result} to its leaf cases — the {@code permits} list and
     * the set of case classes that {@code implements} it. A named-sum output is already a sealed
     * interface (§jvm-sum) and a single-case output uses that case's own type, so neither gets one. Case
     * order is sorted for deterministic bytecode.
     */
    /**
     * A bridge case takes a class name in this module (spec §jvm-anonymous-union), so it is subject to the same rule
     * as every other name this module emits: no two of them may be one class. {@code YenCase} is a
     * name a model may well have declared, and {@code IntCase} / {@code DateCase} the same, so this
     * is reported rather than reserved — the collision is decided by what the module holds, and a
     * name nothing collides with stays available.
     *
     * <p>Three ways to collide: with a data this module declares, with the class a behavior
     * capitalizes into (spec §jvm-behavior), and with another bridge case. The last is two members of one
     * spelling from two modules — refused within a union by the member-name rule, and reaching here
     * when they are members of two different unions of this module.
     */
    private void rejectBridgeCaseCollisions(Ast.Module module, Map<TypeName, List<String>> bridgeCases,
                                            Map<String, List<TypeName>> behaviorResults,
                                            Set<String> localTypes, Map<String, String> behaviorClassOwner) {
        Map<String, TypeName> byBridgeName = new LinkedHashMap<>();
        for (Map.Entry<TypeName, List<String>> e : bridgeCases.entrySet()) {
            TypeName member = e.getKey();
            String bridge = CodegenContext.bridgeCaseName(member);
            Ast.BehaviorDef owner = behaviorOf(module, e.getValue().get(0));
            SourcePos pos = owner != null ? owner.pos() : module.pos();
            String what = owner != null ? owner.name() : e.getValue().get(0);
            TypeName sameName = byBridgeName.put(bridge, member);
            if (sameName != null) {
                throw CompileException.of(Diagnostic.say(new ModuleMessage.TwoMembersJoinThroughOneCaseClass(sameName.qualified(), member.qualified(), bridge))
                                .at(pos)
                                .hint(new ModuleMessage.AMemberGoesByItsOwnNameWithCaseAfterIt()).build());
            }
            boolean aData = localTypes.contains(bridge);
            boolean aBehavior = behaviorClassOwner.containsKey(bridge);
            if (aData || aBehavior) {
                String other = aData ? bridge : behaviorClassOwner.get(bridge);
                throw CompileException.of(Diagnostic.at(pos)
                                .say(aData
                                        ? new ModuleMessage.AMemberReachesTheUnionThroughAData(what,
                                                member.name(), bridge, other)
                                        : new ModuleMessage
                                                .AMemberReachesTheUnionThroughABehavior(what,
                                                        member.name(), bridge, other))
                                .hint(new ModuleMessage.RenameTheMemberOrTheTypeItCollidesWith(bridge)).build());
            }
        }
    }

    /**
     * A behavior with a union output is generated as a sealed interface named after it, so that name
     * is subject to the rule every other name this module emits is subject to: no two of them may be
     * one class. Two ways to collide — with a data this module declares, and with the class another
     * behavior capitalizes into. Two result unions cannot collide with each other, their behaviors
     * having already been rejected for capitalizing into one class.
     */
    private void rejectResultUnionCollisions(Ast.Module module, Map<String, List<TypeName>> behaviorResults,
                                             Set<String> localTypes, Map<String, String> behaviorClassOwner) {
        for (String resultName : behaviorResults.keySet()) {
            Ast.BehaviorDef owner = behaviorOf(module, resultName);
            SourcePos pos = owner != null ? owner.pos() : module.pos();
            String what = owner != null ? owner.name() : resultName;
            if (localTypes.contains(resultName)) {
                throw CompileException.of(Diagnostic
                                .at(pos)
                                .hint(new BehaviorMessage.AUnionOutputReachesJavaThroughThatName(resultName)).say(new BehaviorMessage.AUnionOutputsInterfaceCollidesWithAData(what, resultName)).build());
            }
            String behavior = behaviorClassOwner.get(resultName);
            if (behavior != null) {
                throw CompileException.of(Diagnostic
                                .at(pos)
                                .hint(new BehaviorMessage.AUnionOutputReachesJavaThroughThatName(resultName)).say(new BehaviorMessage.AUnionOutputsInterfaceCollidesWithABehavior(what, resultName, behavior)).build());
            }
        }
    }

    /** The behavior whose generated result union is {@code resultName}, or null when none is. */
    private Ast.BehaviorDef behaviorOf(Ast.Module module, String resultName) {
        for (Ast.BehaviorDef bd : module.behaviors()) {
            if (CodegenContext.behaviorResultClass(bd.name()).equals(resultName)) {
                return bd;
            }
        }
        return null;
    }

    private Map<String, List<TypeName>> behaviorResultInterfaces(Ast.Module module,
                                                                 Map<String, Sig> sigs) {
        Map<String, List<TypeName>> results = new LinkedHashMap<>();
        for (Ast.BehaviorDef bd : module.behaviors()) {
            Sig sig = sigs.get(bd.name());
            if (sig == null || !(sig.outputType() instanceof Type.Union)) {
                continue;
            }
            List<TypeName> members = new ArrayList<>(TypeOps.leafCases(sig.outputType(), symbols));
            Collections.sort(members);
            results.put(CodegenContext.behaviorResultClass(bd.name()), members);
        }
        return results;
    }

    /**
     * Generates the sealed interface for a behavior's anonymous union output (spec §jvm-anonymous-union). A member
     * this module declared is permitted as itself; any other is permitted as its bridge case. The
     * interface carries the union's {@code encoder()}: a Java consumer that switches reads a case
     * and uses that case's own codec, and one that wants the answer as it crosses a boundary asks
     * the union, which writes the discriminator no member writes on itself.
     */
    private byte[] generateBehaviorResult(String resultName, List<TypeName> members) {
        ClassDesc cdR = cd(resultName);
        List<ClassDesc> caseCds = new ArrayList<>();
        for (TypeName member : members) {
            caseCds.add(ctx.resultMemberClass(member));
        }
        return build(cdR, cb -> {
            cb.withFlags(ClassFile.ACC_PUBLIC | ClassFile.ACC_INTERFACE | ClassFile.ACC_ABSTRACT);
            cb.with(PermittedSubclassesAttribute.ofSymbols(caseCds));
            codec.emitResultUnionEncoderFactory(cb, resultName, members);
        });
    }


    private Type successType(Ast.RetType ret) {
        return ctx.successType(ret);
    }

    private ClassDesc cd(String typeName) {
        return ctx.cd(typeName);
    }

    /** The class a behavior is emitted under (spec §jvm-behavior). Anything that has to name that class from
     * outside codegen — publishing a module's declarations onto it, say — asks here rather than
     * repeating the rule, so the name a reader is sent to is the name that was emitted. */
    public static String behaviorClass(String name) {
        return CodegenContext.behaviorClass(name);
    }

    /** The class a behavior's anonymous union output is emitted under (spec §jvm-anonymous-union), for the same
     * reason {@link #behaviorClass} is public: the name is decided here. */
    public static String behaviorResultClass(String name) {
        return CodegenContext.behaviorResultClass(name);
    }

    /**
     * The version of what another module reaches across the boundary into a compiled one.
     *
     * <p>Two things are under it. One is what this package emits: the {@code __construct} descriptors
     * and visibilities, the codecs, a behavior's class and its methods, an output union's case names,
     * and the runtime types in those signatures. A change to any of it makes a previously built jar
     * unusable and has to move this number with it; a change confined to the inside of a generated
     * method does not touch it.
     *
     * <p>The other is the source a jar carries for a reader to compile: a data's invariant, and the
     * body of every value and helper the module publishes ({@link
     * souther.compiler.meta.ModuleMetadata}). Those are read back by whichever compiler imports the
     * module, so what the front end makes of them is a promise the jar carries too — a change to how
     * one of those bodies is read moves this number as surely as a change to a descriptor does, and
     * it is the front end's change rather than this package's. {@link
     * souther.compiler.meta.PublishedModule} refuses a jar that disagrees, so the disagreement is
     * reported as what it is instead of surfacing as an unresolved name inside a body nobody wrote.
     *
     * <p>A third thing arrived with version 6: what a published helper's declaration promises. A helper
     * written without {@code partial} carries the termination guarantee for everything it reaches (spec
     * §fn-rules), so a reader answers the question off the word on the declaration and does not walk the
     * closure behind it. That only holds if the writer enforced the rule, which is why an older jar —
     * whose unmarked helper may reach a {@code partial} one — is refused rather than read.
     *
     * <p>Version 7 narrows what a published behavior's signature may be: an optional does not stand
     * anywhere in a behavior's boundary shape (spec §external-representation). A reader takes an
     * imported declaration as one the writer was held to, so a jar built when a parameter could be
     * written {@code Option<Int>} carries a signature this compiler would refuse, and calling it would
     * put the runtime's {@code Option} across a boundary that no longer admits one.
     *
     * <p>Version 8 narrows it again: a named type standing in a behavior's boundary is one a model
     * declares, so the vocabulary the language keeps for its own operations — what a division by zero
     * answers with, what a rounding takes, the reserved {@code Raw} — is not carried across one. A
     * module written without an {@code exposing} line publishes every behavior it declares, so a jar
     * built before this carries a public {@code Behavior<souther.runtime.DivisionByZero, …>} that this
     * compiler refuses to write.
     *
     * <p>Version 9 asks those rules of every signature rather than of every declaration. Admitting
     * what a boundary carries is now the making of the signature, so a composition's merged output is
     * subject to it — a case that retired out of a stage's answer is a name in what crosses like any
     * other — and so is a declaration read back from a jar. A jar built before this was trusted for
     * both: what its compiler checked was what its author wrote, and a composition it published, or a
     * declaration a reader takes on faith, was never asked.
     *
     * <p>Version 10 moves where the {@code "value"} envelope is written. A derived codec is now the
     * standalone representation of its type, and a sum's encoding adds what membership in that sum
     * requires (spec §sum-discrimination); before, a newtype that some sum listed had the envelope
     * written into its own codec, so what the type published depended on a declaration elsewhere. A
     * jar built before this carries a {@code $Enc} that writes {@code {"value": …}} and a
     * {@code $Dec} that demands it, which this compiler's sum encoder would wrap a second time and
     * its sum decoder would hand the inner value to.
     *
     * <p>Version 11 narrows what a string literal may be: it ends on the line it began on, and a
     * backslash is read only before {@code n}, {@code t}, {@code r}, a quote and another backslash
     * (spec §string-literal). A published helper's body travels in the jar as source and is read
     * back by the importing compiler (spec §exposed-values), so what a literal may be is part of
     * what a compiled module promises. A jar built before this may carry a body this compiler
     * cannot read — a literal that ran past its line — or one whose backslash the older compiler
     * dropped in silence and this one refuses.
     *
     * <p>Version 12 widens the same thing rather than narrowing it: {@code <-} is not a token, so a
     * {@code <} and the negation after it need no space between them and {@code a<-1} is a body this
     * compiler admits and copies into a jar as written. A reader is held to an equal version and not
     * merely a lower one, which is what makes the widening matter: an older compiler would take the
     * module for one it understands and then fail on a body whose {@code <-} its own lexer still
     * glues into a token no production of its own reads.
     *
     * <p>Version 13 settles what a name is made of: {@code XID_Start XID_Continue*} at Unicode
     * 17.0.0 (spec §identifier). It moves in both directions. A jar built before this may carry a
     * body naming something this compiler will not read — a name holding {@code $}, or beginning
     * with {@code _} — because the older compiler read Java's identifier rule. And a body written
     * now may name something an older compiler cannot read, since a name may hold a character
     * outside the basic plane, which the older one scanned by UTF-16 unit and refused. The same
     * number covers a later Unicode version, which admits names that were not names before.
     *
     * <p>Version 14 narrows what a temporal carries, and widens what the primitives are. A
     * {@code DateTime} is held to the second, so a jar built before this accepts
     * {@code "09:30:45.123"} at a field this compiler's decoder refuses, and a caller reading the
     * older jar's promise would be told a value crossed that no longer does. {@code Time} and
     * {@code Instant} are new primitives, so a jar built now may declare a boundary shape an older
     * compiler has no type for at all.
     */
    public static final int BOUNDARY_VERSION = 14;

    /** The class a module's own declarations are published on. It carries nothing but them. */
    public static String moduleClassName(String moduleName) {
        return moduleName + ".$Module";
    }

    /** Emits {@link #moduleClassName}, carrying {@code declarations}. What it says is the caller's;
     * that it is built like every other generated class — the same Java floor, the same
     * {@code SourceFile} — is this package's. */
    public static byte[] moduleClass(String moduleName, Annotation declarations) {
        return Descriptors.build(ClassDesc.of(moduleClassName(moduleName)), cb -> cb
                .withFlags(ClassFile.ACC_FINAL | ClassFile.ACC_SYNTHETIC)
                .with(RuntimeInvisibleAnnotationsAttribute.of(declarations)));
    }

    private ClassDesc cdBehavior(String name) {
        return ctx.cdBehavior(name);
    }

    private ClassDesc cdBehaviorImpl(String name) {
        return ctx.cdBehaviorImpl(name);
    }


    private ClassDesc caseClass(TypeName typeName) {
        return ctx.caseClass(typeName);
    }

    // --- sum data (sealed interface) ---

    /** Emits a {@code static} factory that returns a fresh instance of {@code impl}. */
    // --- behaviors ---

    /**
     * Generates a behavior implemented by a {@code fn} (spec §fn-declaration). The behavior's inputs are the
     * {@code apply} arguments; its {@code depends on} are injected fields (§depends-on). The {@code fn}'s
     * leading parameters name the inputs (their types come from the behavior); the trailing ones
     * name the injected behaviors and are resolved as inline calls, not bound as locals.
     */
    private byte[] generateSpecFn(Ast.SpecBehavior spec, Ast.FnDef fn, Set<String> requiredNames,
                                  Map<String, Type> requiredSuccess, Map<String, List<Type>> requiredParam) {
        ClassDesc cdB = cdBehaviorImpl(spec.name());   // the $Impl behind the public interface
        int n = spec.params().size();
        // declared dependencies, validated to equal what the fn calls (E1602/E1603); the same order is
        // used by pipeline callers (requirementSets), so the injected fields line up.
        List<String> injected = requiredBy(spec);
        ClassDesc[] applyParams = new ClassDesc[n];
        for (int i = 0; i < n; i++) {
            applyParams[i] = CD_Object;
        }
        MethodTypeDesc mtdApply = MethodTypeDesc.of(CD_Object, applyParams);
        return build(cdB, cb -> {
            cb.withFlags(pub(spec.name()) | ClassFile.ACC_FINAL | ClassFile.ACC_SUPER);
            // implements its public interface (which itself extends Behavior for a single-input one)
            cb.withInterfaceSymbols(cdBehavior(spec.name()));
            emitInjection(cb, cdB, injected);
            cb.withMethodBody("apply", mtdApply, ClassFile.ACC_PUBLIC, code -> {
                BodyGen gen = new BodyGen(ctx, code, null, cdB, n + 1);
                // The one body a coverage plan is made from, so the one body whose arms are counted.
                gen.armsAreCounted();
                gen.injectsInto(successType(spec.ret()));
                gen.requireds(requiredNames, requiredSuccess, requiredParam);
                for (int i = 0; i < n; i++) {
                    // the fn's leading param names the input; its type comes from the behavior
                    Type pt = successType(spec.params().get(i).type());
                    code.aload(i + 1);
                    int slot = gen.slot(pt);
                    unbox(code, pt, slot);
                    gen.bind(fn.params().get(i).binder(), slot, pt);
                }
                // thread the behavior's declared output so a tail-position fold over an empty seed
                // materialises its step at the output type, not a bottom (issue #70)
                gen.emitTail(elaborated(checked.behaviorBodies(), fn.name()),
                        cdB, requiredNames, requiredSuccess, successType(spec.ret()));
            });
            if (n != 1) {
                List<Type> pts = new ArrayList<>();
                for (Ast.Param p : spec.params()) {
                    pts.add(successType(p.type()));
                }
                emitTypedApplyBridge(cb, cdB, typedApplyDesc(spec.name(), pts, successType(spec.ret())));
            }
        });
    }


    /**
     * A composition's own signature, worked out when the module's signatures were.
     *
     * <p>A composition resting on a stage that names nothing has none — it was abandoned there. A
     * module holding one is not emitted, so reaching this with no signature means the gate that
     * decides let something through that has no meaning, and there is nothing to emit for it.
     */
    private static Sig declaredSig(Ast.PipeBehavior pipe, Map<String, Sig> sigs) {
        Sig sig = sigs.get(pipe.name());
        if (sig == null) {
            throw new IllegalStateException("`" + pipe.name() + "` reached codegen with no signature,"
                    + " at " + pipe.pos());
        }
        return sig;
    }

    /** The behaviors a spec declares it depends on, by the name each is reached by. */
    private static List<String> requiredBy(Ast.SpecBehavior spec) {
        List<String> names = new ArrayList<>();
        for (Ast.Var req : spec.dependsOn()) {
            names.add(req.bare());
        }
        return names;
    }

    private byte[] generatePipe(Ast.PipeBehavior pipe, Set<String> requiredNames,
                                Map<String, Sig> sigs, Map<String, List<String>> behaviorDeps,
                                Map<String, List<Ast.Var>> pipeStages) {
        ClassDesc cdP = cdBehaviorImpl(pipe.name());   // the $Impl behind the public interface
        // Flatten nested pipeline stages so the routing is over leaf behaviors (spec §type-routing): a named
        // intermediate `half = split >-> work` inlines to `split, work`, which keeps a retired case
        // retired across the composition, making `>->` associative.
        List<Ast.Var> flat = PipelineSigs.flattenStages(pipe.stages(), pipeStages, pipe.pos());
        // the pipeline's injected fields are the union of its stages' requirements (spec
        // §composition-with-requirements)
        List<String> reqStages = behaviorDeps.getOrDefault(pipe.name(), List.of());
        // the pipeline takes whatever its first stage takes (spec §sequential-composition)
        int arity = PipelineSigs.stageSig(flat.get(0), sigs, symbols, pipe.pos()).inputTypes().size();
        ClassDesc[] applyParams = new ClassDesc[arity];
        java.util.Arrays.fill(applyParams, CD_Object);
        MethodTypeDesc mtdApply = MethodTypeDesc.of(CD_Object, applyParams);

        return build(cdP, cb -> {
            cb.withFlags(pub(pipe.name()) | ClassFile.ACC_FINAL | ClassFile.ACC_SUPER);
            // implements its public interface (which itself extends Behavior for a single-input one)
            cb.withInterfaceSymbols(cdBehavior(pipe.name()));
            emitInjection(cb, cdP, reqStages);

            cb.withMethodBody("apply", mtdApply, ClassFile.ACC_PUBLIC, code -> {
                // slot 1 always holds the running value (an output case, as an Object).
                List<Ast.Var> stages = flat;
                // stage 0 consumes the pipeline's arguments unconditionally
                Type mainline = PipelineSigs.stageSig(stages.get(0), sigs, symbols, pipe.pos()).outputType();
                applyFirstStage(code, cdP, stages.get(0).bare(), arity, requiredNames, behaviorDeps,
                        mainline, arity + 1);
                Label end = code.newLabel();
                for (int i = 1; i < stages.size(); i++) {
                    String stage = stages.get(i).bare();
                    Sig g = PipelineSigs.stageSig(stages.get(i), sigs, symbols, pipe.pos());
                    if (TypeOps.isDataLike(mainline)) {
                        // Apply g only when the running value is one of the main-line cases it
                        // accepts. Anything else has left the main line: jump to the end rather
                        // than offering it to the stages after this one (spec §type-routing). Branching to
                        // the end is what makes a retired case unreachable without tagging it — the
                        // same case type may legitimately reappear on the main line downstream.
                        List<TypeName> accepted = PipelineSigs.mainlineCases(mainline, g, symbols);
                        Label doApply = code.newLabel();
                        for (TypeName caseName : accepted) {
                            code.aload(1);
                            code.instanceOf(caseClass(caseName));
                            code.ifne(doApply);
                        }
                        code.goto_(end);
                        code.labelBinding(doApply);
                        applyStage(code, cdP, stage, requiredNames, behaviorDeps, g.outputType(), arity + 1);
                    } else {
                        applyStage(code, cdP, stage, requiredNames, behaviorDeps, g.outputType(), arity + 1);
                    }
                    mainline = PipelineSigs.stageOut(mainline, g, symbols, pipe.pos());
                }
                code.labelBinding(end);
                code.aload(1);
                // The composition's own return: the running value is a Souther value, and this is
                // where it becomes a member of the union this composition answers with.
                ResultBoundary.inject(code, ctx, ctx.bridgedMembers(declaredSig(pipe, sigs).outputType()),
                        arity + 1);
            });
            if (arity != 1) {
                Sig sig = declaredSig(pipe, sigs);
                emitTypedApplyBridge(cb, cdP, typedApplyDesc(pipe.name(), sig.inputTypes(), sig.outputType()));
            }
        });
    }

    /**
     * Applies the first stage to the pipeline's own arguments, leaving the result in slot 1.
     *
     * <p>Only this stage may take other than one input (spec §sequential-composition). Such a behavior does not
     * implement {@code Behavior} — that interface takes one value — so it is called on its own
     * class rather than through the interface. An injected one is that class: the pipeline holds it
     * in the field it was bound to, and its {@code apply} is typed rather than erased (issue #57),
     * so the arguments are cast from the erased {@code apply(Object,…)} this body lives on. A
     * zero-input stage takes that same path with nothing to cast.
     */
    private void applyFirstStage(CodeBuilder code, ClassDesc cdP, String stage, int arity,
                                 Set<String> requiredNames, Map<String, List<String>> behaviorDeps,
                                 Type stageOut, int slot) {
        if (arity == 1) {
            applyStage(code, cdP, stage, requiredNames, behaviorDeps, stageOut, slot);
            return;
        }
        pushStage(code, cdP, stage, requiredNames, behaviorDeps);
        if (ctx.isStandaloneRequired(stage)) {
            MethodTypeDesc desc = ctx.requiredApplyDesc(stage);
            for (int i = 0; i < arity; i++) {
                code.aload(i + 1);
                ClassDesc param = desc.parameterType(i);
                if (!param.equals(CD_Object)) {
                    code.checkcast(param);
                }
            }
            code.invokevirtual(cdBehavior(stage), "apply", desc);
            projectStage(code, stage, stageOut, slot);
            code.astore(1);
            return;
        }
        for (int i = 0; i < arity; i++) {
            code.aload(i + 1);
        }
        ClassDesc[] params = new ClassDesc[arity];
        java.util.Arrays.fill(params, CD_Object);
        // a multi-input first stage with a `let` is a fn/pipe behavior; call the erased apply on its $Impl
        code.invokevirtual(cdBehaviorImpl(stage), "apply", MethodTypeDesc.of(CD_Object, params));
        projectStage(code, stage, stageOut, slot);
        code.astore(1);
    }

    /** Applies one pipeline stage to the running value in slot 1, storing the result back. A stage
     * is a behavior, or a {@code Type.decoder}/{@code Type.encoder} boundary codec (spec §sequential-composition). */
    private void applyStage(CodeBuilder code, ClassDesc cdP, String stage, Set<String> requiredNames,
                            Map<String, List<String>> behaviorDeps, Type stageOut, int slot) {
        // decode/encode are boundary edges, not pipeline stages (spec §sequential-composition): `>->` composes
        // behaviors only.
        pushStage(code, cdP, stage, requiredNames, behaviorDeps);
        code.aload(1);
        code.invokeinterface(CD_Behavior, "apply", MTD_apply);
        projectStage(code, stage, stageOut, slot);
        code.astore(1);
    }

    /** A stage answered with a member of its own result union; the running value the next stage sees
     * is a Souther value again (spec §jvm-anonymous-union). The same conversion a body does after a call. */
    private void projectStage(CodeBuilder code, String stage, Type stageOut, int slot) {
        ResultBoundary.project(code, ctx, stage, ctx.bridgedMembersOf(stage, stageOut), slot);
    }

    /** Pushes the behavior object for a pipeline stage: an injected required field, or a fresh
     * body-behavior instance constructed with the required dependencies it declares (spec
     * §composition-with-requirements). */
    private void pushStage(CodeBuilder code, ClassDesc cdP, String stage, Set<String> requiredNames,
                           Map<String, List<String>> behaviorDeps) {
        if (requiredNames.contains(stage)) {
            code.aload(0);
            code.getfield(cdP, stage, ctx.requiredFieldType(stage));
            return;
        }
        ClassDesc cdStage = cdBehaviorImpl(stage);   // instantiate the $Impl, not the interface
        code.new_(cdStage);
        code.dup();
        List<String> deps = behaviorDeps.getOrDefault(stage, List.of());
        ClassDesc[] ctorParams = new ClassDesc[deps.size()];
        for (int i = 0; i < deps.size(); i++) {
            // a multi-arg injected dependency is stored/wired by its base class, not the unary
            // Behavior (issue #57) — the field descriptor and the stage $Impl ctor param must match
            ClassDesc depType = ctx.requiredFieldType(deps.get(i));
            code.aload(0);
            code.getfield(cdP, deps.get(i), depType);   // reuse the pipeline's injected field
            ctorParams[i] = depType;
        }
        code.invokespecial(cdStage, "<init>", MethodTypeDesc.of(ConstantDescs.CD_void, ctorParams));
    }

    // --- value class members ---

    // --- source compatibility: which extra source decoders a type's shape supports (spec §codec-generation) ---

    // --- $Dec class ---

    /** Pushes each field value in declaration order, sourced from an explicit init or a spread. */

    // --- $Enc class ---

    // --- helpers ---

    private void unbox(CodeBuilder code, Type type, int slot) {
        JvmTypes.unbox(code, type, slot, ctx);
    }

}
