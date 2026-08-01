package souther.compiler.codegen;

import souther.compiler.check.Symbols;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;
import souther.compiler.ast.Ast;
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
 * The ClassFile-API backend (spec sections 19, 20). Emits JVM bytecode directly for each
 * {@code data}: the value class (package-private ctor + invariant-checking
 * {@code __construct}) and nested {@code $Dec}/{@code $Enc} classes. Fields may reference
 * other data types; object decoders accumulate every field error (spec sections 15, 27.7).
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

    public static Map<String, byte[]> generate(Ast.Module module, TypeChecker.Checked checked) {
        return generate(module, TypeChecker.symbols(module), Map.of(), Map.of(), Set.of(), Map.of(),
                Requirements.of(module, Set.of()), checked, Map.of());
    }

    /** Generates a module's classes. {@code symbols} covers own plus imported definitions;
     * {@code typePackage} maps an imported type or behavior name to its declaring module (spec 4);
     * {@code importedSigs} carries imported behaviors' signatures so a composition can name one as
     * a stage (spec 14); {@code importedInjected} are imported injection-target behaviors, which a
     * composition here inherits as requirements to inject and bind (spec 13.2, 14.3);
     * {@code requirements} says what each behavior takes injected and in what order — the answer the
     * example verifier reads too, so a fake reaches the parameter this constructor binds it to;
     * {@code checked} carries the type checker's elaborated bodies, which is what the emitter reads
     * instead of inferring types again (issue #81); {@code dischargeInvariants} carries this module's
     * invariant clauses in the representation the language's own operations survive in, which is what a
     * derived decoder's constraint mapping reads (spec §decoder-error). */
    public static Map<String, byte[]> generate(Ast.Module module, Symbols symbols,
                                               Map<String, String> typePackage,
                                               Map<String, Sig> importedSigs,
                                               Set<String> importedInjected,
                                               Map<String, ReqSig> calleeSigs,
                                               Map<String, List<BehaviorRequirement>> requirements,
                                               TypeChecker.Checked checked,
                                               Map<TypeName, List<Ast.InvariantClause>> dischargeInvariants) {
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
        // (exposing is type-granular, spec 19.4), so every entry that reaches codegen is a bare name.
        Set<String> exposed = new HashSet<>(module.exposing());
        // After the Lower stage the only non-behavior fns left are recursive helpers (spec 13.1);
        // each is lowered to a static method on the module's `$Fns` class rather than inlined.
        Set<String> behaviorNames = new HashSet<>();
        for (Ast.BehaviorDef bd : module.behaviors()) {
            behaviorNames.add(bd.name());
        }
        Map<String, Ast.FnDef> recHelpers = new LinkedHashMap<>();
        for (Ast.FnDef fn : module.fns()) {
            if (!behaviorNames.contains(fn.name())) {
                recHelpers.put(fn.name(), fn);
            }
        }
        CodegenContext ctx = new CodegenContext(module.name(), symbols, caseToSums, typePackage,
                module.exposing().isEmpty(), exposed, recHelpers);
        ctx.setDischargeInvariants(dischargeInvariants);
        Backend b = new Backend(ctx, checked);
        // A behavior's class capitalizes its first letter (spec 19.5). Data names are already
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
                throw CompileException.of(
                        Diagnostic.of(null, "check.behavior.collision.data").title("check.duplicate.title")
                                .at(bd.pos()).args(bd.name(), cls).build(),
                        "behavior `" + bd.name() + "`'s first letter is capitalized to form the JVM class `"
                                + cls + "` (spec 19.5), which collides with data `" + cls
                                + "`; rename one so their class names differ");
            }
            String prev = behaviorClassOwner.put(cls, bd.name());
            if (prev != null) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.behavior.collision.behavior").title("check.duplicate.title")
                                .at(bd.pos()).args(prev, bd.name(), cls).build(),
                        "behaviors `" + prev + "` and `" + bd.name() + "` both capitalize to the same JVM"
                                + " class `" + cls + "` (spec 19.5); rename one so their class names differ");
            }
        }
        // A behavior whose output is an anonymous union gets a generated sealed interface
        // <behavior名>Result that its cases implement (spec 19.8). Register those case->interface links
        // in caseToSums before the data classes are generated, so each case class picks the interface
        // up in withInterfaceSymbols. The interface classes themselves are emitted below.
        Map<String, List<TypeName>> behaviorResults = b.behaviorResultInterfaces(module, importedSigs);
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
        Map<String, byte[]> out = new LinkedHashMap<>();
        behaviorResults.forEach((resultName, members) -> {
            out.put(module.name() + "." + resultName, b.generateBehaviorResult(resultName, members));
            out.put(module.name() + "." + resultName + "$Enc",
                    b.codec.generateResultUnionEncoder(resultName, members));
        });
        bridgeCases.forEach((member, unions) ->
                out.put(module.name() + "." + CodegenContext.bridgeCaseName(member),
                        b.value.generateBridgeCase(member, unions, out)));
        for (Ast.Def def : module.defs()) {
            switch (def) {
                case Ast.Data data -> b.value.generateData(data, out);
                case Ast.SumData sum -> b.value.generateSum(sum, out);
                case Ast.UnitData unit -> b.value.generateUnit(unit, out);
            }
        }
        // Behavior fn bodies arrive with their helper calls already inlined (the Lower stage,
        // ADR-0021); the backend emits them as-is and never lowers a helper on its own.
        Map<String, Ast.FnDef> fns = new HashMap<>();
        for (Ast.FnDef fn : module.fns()) {
            fns.put(fn.name(), fn);
        }
        // Injection targets (spec 13.2): a SpecBehavior with no matching fn. Each becomes an
        // abstract base class a Java implementation extends (13.3). Imported injection targets
        // (their base lives in the declaring module) are requirements too, so a composition here
        // injects and binds them (spec 14.3) — but no base is generated for them here.
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
                // to build it (spec 2.7), and unlike a unit it cannot be told apart from a decoded
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
                out.put(module.name() + "." + behaviorClass(spec.name()),
                        b.generateRequiredBase(spec.name(), unitCases, dataConstructs,
                                reqParams, b.successType(spec.ret())));
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
            for (Ast.ValueRef req : spec.dependsOn()) {
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
                    requiredParam.put(name, imported.ins());
                    requiredSuccess.put(name, imported.out());
                }
            }
        }
        for (String name : importedInjected) {
            Sig sig = importedSigs.get(name);
            if (sig != null) {
                requiredParam.put(name, sig.ins());
                requiredSuccess.put(name, sig.out());
            }
        }
        // The unary-vs-multi dispatch for required behaviors reads these; set once, so the base class,
        // the $Impl field/ctor, the bind factory, and every call site agree (issue #57).
        b.ctx.setRequiredSignatures(requiredParam, requiredSuccess);
        // A behavior that depends on nothing is called by being built where it is called, so it is not
        // in the injection maps above; what a call site needs is the signature it was typed against.
        b.ctx.setCalleeSignatures(calleeSigs);
        Map<String, Sig> sigs = PipelineSigs.signatures(module, b.symbols, importedSigs);
        // What each behavior takes injected, worked out once and read here and at an example
        // (Bodies.Requirements): the order is this constructor's parameter order.
        Map<String, List<String>> behaviorDeps = new LinkedHashMap<>();
        for (Map.Entry<String, List<BehaviorRequirement>> e : requirements.entrySet()) {
            behaviorDeps.put(e.getKey(), Requirements.names(e.getValue()));
        }
        Map<String, List<Ast.ValueRef>> pipeStages = PipelineSigs.pipelineStages(module);
        for (Ast.BehaviorDef bd : module.behaviors()) {
            switch (bd) {
                case Ast.SpecBehavior spec -> {
                    Ast.FnDef fn = fns.get(spec.name());
                    if (fn != null) {
                        // a fn-implemented behavior: the $Impl holds the logic, the public interface
                        // (behaviorClass) is what Java code declares (spec 19.8).
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
                    // else: injection target — its abstract base was generated above (spec 13.3)
                }
                case Ast.PipeBehavior pipe -> {
                    out.put(module.name() + "." + CodegenContext.behaviorImplClass(pipe.name()),
                            b.generatePipe(pipe, requiredNames, sigs, behaviorDeps, pipeStages));
                    Sig sig = declaredSig(pipe, sigs);
                    out.put(module.name() + "." + behaviorClass(pipe.name()),
                            b.generateBehaviorInterface(pipe.name(), sig.ins(), sig.out(),
                                    behaviorDeps.getOrDefault(pipe.name(), List.of())));
                }
            }
        }
        if (!recHelpers.isEmpty()) {
            out.put(module.name() + ".$Fns", b.generateRecursiveHelpers(recHelpers));
        }
        out.putAll(b.ctx.synthClasses());   // escaping lambdas compiled to Fn classes (spec §blocks)
        return out;
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
     * class (spec 13.1). Each helper's declared parameter and return types are boxed as {@code Object}
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
                cb.withMethodBody(CodegenContext.helperMethod(h.name()),
                        MethodTypeDesc.of(CD_Object, params), ClassFile.ACC_STATIC,
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
     * interface (spec 19.5). {@code of()} for a behavior with no {@code depends on}; {@code bind(<named
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
     * Generates the abstract base class for a required behavior (spec 13.3): an abstract
     * {@code Behavior} that a Java implementation extends. The base exposes a {@code protected}
     * factory for what the implementation may build (spec 2.1). The two kinds are sourced differently.
     * A unit output case gets a no-arg factory: a unit has no invariant to validate, so it is built
     * directly, and it is taken from the output cases (an injected behavior may leave {@code constructs}
     * implicit, and a unit is safe to hand out either way). A field-bearing type gets a typed factory
     * built through its {@code __construct} so the invariant is checked, but only when the behavior
     * declares it in {@code constructs}: that declaration is the authority to build it (spec 2.7), and
     * unlike a unit it cannot be told apart from a decoded pass-through output by shape alone. The typed
     * factory lets the implementation compose already-held values into its declared output without
     * round-tripping through the decoder. The data constructors stay non-public, so a subclass builds
     * exactly these and nothing else, from any package.
     *
     * <p>When both the input and output map to a concrete reference type, the base carries a
     * generic {@code Behavior<In, Out>} signature (spec 19.8, 24) — {@code Out} is the {@code <名>Result}
     * interface for an anonymous union output — so a Java author writes the real return type rather
     * than {@code Object}. If either side is a list/option/map (no single reference class), the
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
     * {@code __construct}, so the invariant is checked and a violation aborts (spec 7.3) — the same
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
     * (List/Set/Map/Option), else {@code null}. Mirrors the value-class accessor signature (spec 8.5)
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
     * The public interface a Java caller declares for a fn/pipe behavior (spec 19.8). It hides the
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
     * Behavior-result interfaces to generate (spec 19.8): for each behavior whose output is an
     * anonymous union, maps {@code <behavior名>Result} to its leaf cases — the {@code permits} list and
     * the set of case classes that {@code implements} it. A named-sum output is already a sealed
     * interface (19.3) and a single-case output uses that case's own type, so neither gets one. Case
     * order is sorted for deterministic bytecode.
     */
    /**
     * A bridge case takes a class name in this module (spec 19.8), so it is subject to the same rule
     * as every other name this module emits: no two of them may be one class. {@code YenCase} is a
     * name a model may well have declared, and {@code IntCase} / {@code DateCase} the same, so this
     * is reported rather than reserved — the collision is decided by what the module holds, and a
     * name nothing collides with stays available.
     *
     * <p>Three ways to collide: with a data this module declares, with the class a behavior
     * capitalizes into (spec 19.5), and with another bridge case. The last is two members of one
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
                throw CompileException.of(
                        Diagnostic.of(null, "check.bridge.collision.member").title("check.duplicate.title")
                                .at(pos).args(sameName.qualified(), member.qualified(), bridge)
                                .hint("check.bridge.collision.member.hint").build(),
                        "`" + sameName + "` and `" + member + "` both join a union of this module"
                                + " through a generated case class `" + bridge + "`");
            }
            String collidesWith = localTypes.contains(bridge) ? "check.bridge.collision.data"
                    : behaviorClassOwner.containsKey(bridge) ? "check.bridge.collision.behavior" : null;
            if (collidesWith != null) {
                String other = localTypes.contains(bridge) ? bridge : behaviorClassOwner.get(bridge);
                throw CompileException.of(
                        Diagnostic.of(null, collidesWith).title("check.duplicate.title")
                                .at(pos).args(what, member.name(), bridge, other)
                                .hint("check.bridge.collision.hint", bridge).build(),
                        "the output of `" + what + "` has the member `" + member.name() + "`, which"
                                + " joins the union through a generated case class `" + bridge
                                + "` (spec 19.8), and `" + other + "` already takes that class name");
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
                throw CompileException.of(
                        Diagnostic.of(null, "check.result.collision.data").title("check.duplicate.title")
                                .at(pos).args(what, resultName)
                                .hint("check.result.collision.hint", resultName).build(),
                        "the output of `" + what + "` is a union, generated as a sealed interface `"
                                + resultName + "` (spec 19.8), and `" + resultName
                                + "` already takes that class name");
            }
            String behavior = behaviorClassOwner.get(resultName);
            if (behavior != null) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.result.collision.behavior").title("check.duplicate.title")
                                .at(pos).args(what, resultName, behavior)
                                .hint("check.result.collision.hint", resultName).build(),
                        "the output of `" + what + "` is a union, generated as a sealed interface `"
                                + resultName + "` (spec 19.8), and `" + behavior
                                + "` already capitalizes into that class name");
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
                                                                 Map<String, Sig> importedSigs) {
        Map<String, Sig> sigs = PipelineSigs.signatures(module, symbols, importedSigs);
        Map<String, List<TypeName>> results = new LinkedHashMap<>();
        for (Ast.BehaviorDef bd : module.behaviors()) {
            Sig sig = sigs.get(bd.name());
            if (sig == null || !(sig.out() instanceof Type.Union)) {
                continue;
            }
            List<TypeName> members = new ArrayList<>(TypeOps.leafCases(sig.out(), symbols));
            Collections.sort(members);
            results.put(CodegenContext.behaviorResultClass(bd.name()), members);
        }
        return results;
    }

    /**
     * Generates the sealed interface for a behavior's anonymous union output (spec 19.8). A member
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

    /** The class a behavior is emitted under (spec 19.5). Anything that has to name that class from
     * outside codegen — publishing a module's declarations onto it, say — asks here rather than
     * repeating the rule, so the name a reader is sent to is the name that was emitted. */
    public static String behaviorClass(String name) {
        return CodegenContext.behaviorClass(name);
    }

    /** The class a behavior's anonymous union output is emitted under (spec 19.8), for the same
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
     */
    public static final int BOUNDARY_VERSION = 5;

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
     * Generates a behavior implemented by a {@code fn} (spec 13.1). The behavior's inputs are the
     * {@code apply} arguments; its {@code depends on} are injected fields (12.6). The {@code fn}'s
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
        for (Ast.ValueRef req : spec.dependsOn()) {
            names.add(req.bare());
        }
        return names;
    }

    private byte[] generatePipe(Ast.PipeBehavior pipe, Set<String> requiredNames,
                                Map<String, Sig> sigs, Map<String, List<String>> behaviorDeps,
                                Map<String, List<Ast.ValueRef>> pipeStages) {
        ClassDesc cdP = cdBehaviorImpl(pipe.name());   // the $Impl behind the public interface
        // Flatten nested pipeline stages so the routing is over leaf behaviors (spec 14.2): a named
        // intermediate `half = split >-> work` inlines to `split, work`, which keeps a retired case
        // retired across the composition, making `>->` associative.
        List<Ast.ValueRef> flat = PipelineSigs.flattenStages(pipe.stages(), pipeStages, pipe.pos());
        // the pipeline's injected fields are the union of its stages' requirements (spec 14.3)
        List<String> reqStages = behaviorDeps.getOrDefault(pipe.name(), List.of());
        // the pipeline takes whatever its first stage takes (spec 14.1)
        int arity = PipelineSigs.stageSig(flat.get(0), sigs, symbols, pipe.pos()).ins().size();
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
                List<Ast.ValueRef> stages = flat;
                // stage 0 consumes the pipeline's arguments unconditionally
                Type mainline = PipelineSigs.stageSig(stages.get(0), sigs, symbols, pipe.pos()).out();
                applyFirstStage(code, cdP, stages.get(0).bare(), arity, requiredNames, behaviorDeps,
                        mainline, arity + 1);
                Label end = code.newLabel();
                for (int i = 1; i < stages.size(); i++) {
                    String stage = stages.get(i).bare();
                    Sig g = PipelineSigs.stageSig(stages.get(i), sigs, symbols, pipe.pos());
                    if (TypeOps.isDataLike(mainline)) {
                        // Apply g only when the running value is one of the main-line cases it
                        // accepts. Anything else has left the main line: jump to the end rather
                        // than offering it to the stages after this one (spec 14.2). Branching to
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
                        applyStage(code, cdP, stage, requiredNames, behaviorDeps, g.out(), arity + 1);
                    } else {
                        applyStage(code, cdP, stage, requiredNames, behaviorDeps, g.out(), arity + 1);
                    }
                    mainline = PipelineSigs.stageOut(mainline, g, symbols, pipe.pos());
                }
                code.labelBinding(end);
                code.aload(1);
                // The composition's own return: the running value is a Souther value, and this is
                // where it becomes a member of the union this composition answers with.
                ResultBoundary.inject(code, ctx, ctx.bridgedMembers(declaredSig(pipe, sigs).out()),
                        arity + 1);
            });
            if (arity != 1) {
                Sig sig = declaredSig(pipe, sigs);
                emitTypedApplyBridge(cb, cdP, typedApplyDesc(pipe.name(), sig.ins(), sig.out()));
            }
        });
    }

    /**
     * Applies the first stage to the pipeline's own arguments, leaving the result in slot 1.
     *
     * <p>Only this stage may take other than one input (spec 14.1). Such a behavior does not
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
     * is a behavior, or a {@code Type.decoder}/{@code Type.encoder} boundary codec (spec 14.1). */
    private void applyStage(CodeBuilder code, ClassDesc cdP, String stage, Set<String> requiredNames,
                            Map<String, List<String>> behaviorDeps, Type stageOut, int slot) {
        // decode/encode are boundary edges, not pipeline stages (spec 14.1): `>->` composes
        // behaviors only.
        pushStage(code, cdP, stage, requiredNames, behaviorDeps);
        code.aload(1);
        code.invokeinterface(CD_Behavior, "apply", MTD_apply);
        projectStage(code, stage, stageOut, slot);
        code.astore(1);
    }

    /** A stage answered with a member of its own result union; the running value the next stage sees
     * is a Souther value again (spec 19.8). The same conversion a body does after a call. */
    private void projectStage(CodeBuilder code, String stage, Type stageOut, int slot) {
        ResultBoundary.project(code, ctx, stage, ctx.bridgedMembersOf(stage, stageOut), slot);
    }

    /** Pushes the behavior object for a pipeline stage: an injected required field, or a fresh
     * body-behavior instance constructed with the required dependencies it declares (spec 14.3). */
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

    // --- source compatibility: which extra source decoders a type's shape supports (spec 10.6) ---

    // --- $Dec class ---

    /** Pushes each field value in declaration order, sourced from an explicit init or a spread. */

    // --- $Enc class ---

    // --- helpers ---

    private void unbox(CodeBuilder code, Type type, int slot) {
        JvmTypes.unbox(code, type, slot, ctx);
    }

}
