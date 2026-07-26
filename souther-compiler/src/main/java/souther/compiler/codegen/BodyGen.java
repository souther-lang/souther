package souther.compiler.codegen;

import souther.compiler.check.Symbols;
import souther.compiler.diag.CompileException;
import souther.compiler.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.check.CheckContext;
import souther.compiler.check.Elaborator;
import souther.compiler.check.DataChecker;
import souther.compiler.check.Lower;
import souther.compiler.check.ReqSig;
import souther.compiler.check.Type;
import souther.compiler.check.TypeName;
import souther.compiler.check.TypeOps;
import souther.compiler.core.Core;

import java.lang.classfile.ClassFile;
import java.lang.classfile.CodeBuilder;
import java.lang.classfile.Label;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.MethodTypeDesc;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static souther.compiler.codegen.Descriptors.*;
import static souther.compiler.codegen.JvmTypes.*;

/**
 * Emits a behavior (or helper, or escaping lambda) body: it lowers each Core IR expression to
 * bytecode (ADR-0021), threading a slot environment and the injected requirements in scope. It is the
 * one generator that never reads a codec; the value-class and codec generators build a fresh instance
 * per method and drive it. Name resolution and the synthetic-class sink come from {@link
 * CodegenContext}; the type/bytecode helpers from {@link JvmTypes}; the shipped primitives from
 * {@link Intrinsics}.
 */
final class BodyGen {

    private final CodegenContext ctx;
    /** Aliases of {@link CodegenContext#pkg}/{@link CodegenContext#symbols}, read as bare names. */
    private final String pkg;
    private final Symbols symbols;

    private ClassDesc cd(String typeName) {
        return ctx.cd(typeName);
    }

    private ClassDesc cd(TypeName typeName) {
        return ctx.cd(typeName);
    }

    private ClassDesc matchCaseClass(String caseName) {
        return ctx.matchCaseClass(caseName);
    }

    private Map<String, Type> fieldTypes(Ast.Data data) {
        return ctx.fieldTypes(data);
    }

    private Type successType(Ast.RetType ret) {
        return ctx.successType(ret);
    }

    private ClassDesc jvmType(Type type) {
        return JvmTypes.jvmType(type, ctx);
    }

    private ClassDesc[] fieldDescs(Map<String, Type> fields) {
        return JvmTypes.fieldDescs(fields, ctx);
    }

    private void unbox(CodeBuilder code, Type type, int slot) {
        JvmTypes.unbox(code, type, slot, ctx);
    }

    private void castFromObject(CodeBuilder code, Type type) {
        JvmTypes.castFromObject(code, type, ctx);
    }

        private final CodeBuilder code;
        private final Ast.Data data;
        private final ClassDesc cdName;
        private final Map<String, Var> env = new HashMap<>();
        private int nextSlot;
        private Set<String> reqNames = Set.of();
        private Map<String, Type> reqSuccess = Map.of();
        private Map<String, List<Type>> reqParams = Map.of();
        /** The last line already bound in this method's {@code LineNumberTable}; skips consecutive
         * same-line entries. Fresh per method, since one {@code BodyGen} emits one method's code. */
        private int lastEmittedLine = -1;
        /** Set while emitting a recursive helper method: the helper's name, its parameters, and the
         * label bound at the body entry. A tail-position call to this same helper reassigns the
         * parameter slots and jumps to {@code tcoEntry} rather than recursing, so a self-tail-recursive
         * helper runs in constant stack. Null for any other body (a behavior never self-recurses). */
        private String tcoName;
        private List<Ast.FnParam> tcoParams;
        private Label tcoEntry;

        BodyGen(CodegenContext ctx, CodeBuilder code, Ast.Data data, ClassDesc cdName, int firstSlot) {
            this.ctx = ctx;
            this.pkg = ctx.pkg;
            this.symbols = ctx.symbols;
            this.code = code;
            this.data = data;
            this.cdName = cdName;
            this.nextSlot = firstSlot;
        }

        /** Makes injected required behaviors callable inline from this body (spec 12.2, 13). */
        void requireds(Set<String> names, Map<String, Type> success, Map<String, List<Type>> params) {
            this.reqNames = names;
            this.reqSuccess = success;
            this.reqParams = params;
        }

        /** A {@code ReqSig} view of the injected behaviors in scope, for re-typing a closure body. */
        private Map<String, ReqSig> reqSigs() {
            Map<String, ReqSig> sigs = new HashMap<>();
            for (String n : reqNames) {
                sigs.put(n, new ReqSig(reqParams.get(n), reqSuccess.get(n)));
            }
            return sigs;
        }

        void bind(String name, int slot, Type type) {
            env.put(name, new Var(slot, type));
            nextSlot = Math.max(nextSlot, slot + width(type));
        }

        /** Restores a name to the binding it had before a block shadowed it (or removes it if it had
         * none), so a block's parameters do not leak past the block (see {@link #fold}). */
        private void restore(String name, Var previous) {
            if (previous == null) {
                env.remove(name);
            } else {
                env.put(name, previous);
            }
        }

        int slot(Type type) {
            int s = nextSlot;
            nextSlot += width(type);
            return s;
        }

        /**
         * Emits an AST expression: the codec emitters (decoder, encoder) and a data's invariant are
         * AST-level, so their expressions are elaborated here, at the environment the slots hold,
         * before they are emitted. The types come from the checker either way — a behavior body
         * arrives already elaborated, and these are elaborated on the spot — so there is one
         * implementation of inference and the emitter reads its decisions (issue #81).
         */
        Type expr(Ast.Expr e) {
            return genExpr(elaborate(e, null));
        }

        /** Elaborates an AST expression at this body's environment — the codec emitters hold AST and
         * build the Core nodes they pass back in. It is desugared first, by the same Lower rewrite a
         * body gets, so a surface form with no Core node of its own (a comprehension) reaches the
         * emitter in the shape it emits from. {@code expected} is the type the position wants, as the
         * checker pushes a field's declared type into its initialiser. */
        Core elaborate(Ast.Expr e, Type expected) {
            return Elaborator.elaborate(Lower.desugarExpr(e), typesEnvWithHelpers(),
                    new CheckContext(symbols, data, reqSigs()), expected);
        }

        private void emitFieldRead(CodeBuilder code, TypeName ownerName, String field, Type ft) {
            ClassDesc ownerCd = cd(ownerName);
            if (symbols.isForeign(ownerName)) {
                code.invokevirtual(ownerCd, field, MethodTypeDesc.of(jvmType(ft)));
            } else {
                code.getfield(ownerCd, field, jvmType(ft));
            }
        }

        /** Opens a single-value newtype on the stack to its underlying value (recursively, so a
         * newtype over a newtype reaches the base primitive), returning that value's type; leaves a
         * non-newtype operand untouched. Used so comparison operators read the value a newtype wraps. */
        private Type unwrapNewtypeValue(Type t) {
            if (t instanceof Type.Ref ref
                    && symbols.get(ref.name()) instanceof Ast.Data d && d.newtype()) {
                Type inner = fieldTypes(d).get("value");
                if (inner != null) {
                    emitFieldRead(code, ref.name(), "value", inner);
                    return unwrapNewtypeValue(inner);
                }
            }
            return t;
        }

        private static String captureField(int i) {
            return "c" + i;
        }

        /** Generates a synthetic {@code Fn} class for an escaping lambda: captured free variables become
         * {@code final} fields set by the constructor, and the body compiles into {@code apply}, which
         * unboxes its arguments from the {@code Object[]} and boxes its result (spec §blocks). */
        private byte[] generateLambdaClass(ClassDesc cd, List<String> params, Core body,
                                           List<Type> paramTypes,
                                           Type resultType, List<String> valueNames, List<Type> valueTypes,
                                           List<String> injectedNames, Map<String, Type> reqSuccess,
                                           Map<String, List<Type>> reqParams) {
            return build(cd, cb -> {
                cb.withFlags(ClassFile.ACC_FINAL | ClassFile.ACC_SUPER);
                cb.withInterfaceSymbols(CD_Fn);
                for (int i = 0; i < valueNames.size(); i++) {
                    cb.withField(captureField(i), jvmType(valueTypes.get(i)),
                            ClassFile.ACC_PRIVATE | ClassFile.ACC_FINAL);
                }
                for (String inj : injectedNames) {   // named after the behavior so requiredCall reads it
                    cb.withField(inj, ctx.requiredFieldType(inj), ClassFile.ACC_PRIVATE | ClassFile.ACC_FINAL);
                }
                List<ClassDesc> ctor = new ArrayList<>();
                for (Type t : valueTypes) {
                    ctor.add(jvmType(t));
                }
                for (String inj : injectedNames) {
                    ctor.add(ctx.requiredFieldType(inj));
                }
                cb.withMethodBody("<init>", MethodTypeDesc.of(ConstantDescs.CD_void, ctor.toArray(new ClassDesc[0])),
                        ClassFile.ACC_PUBLIC, code -> {
                    code.aload(0);
                    code.invokespecial(CD_Object, "<init>", MTD_void);
                    int slot = 1;
                    for (int i = 0; i < valueNames.size(); i++) {
                        code.aload(0);
                        load(code, slot, valueTypes.get(i));
                        code.putfield(cd, captureField(i), jvmType(valueTypes.get(i)));
                        slot += width(valueTypes.get(i));
                    }
                    for (String inj : injectedNames) {
                        code.aload(0);
                        code.aload(slot);
                        code.putfield(cd, inj, ctx.requiredFieldType(inj));
                        slot += 1;
                    }
                    code.return_();
                });
                cb.withMethodBody("apply", MTD_Fn_apply, ClassFile.ACC_PUBLIC, code -> {
                    BodyGen g = new BodyGen(ctx, code, null, cd, 2);   // slot 0 = this, slot 1 = the Object[] args
                    if (!injectedNames.isEmpty()) {
                        // the captured behaviors live in this closure's own fields; requiredCall reads
                        // `this.<name>`, so route them the same way the enclosing behavior does
                        Map<String, Type> succ = new HashMap<>();
                        Map<String, List<Type>> parm = new HashMap<>();
                        for (String inj : injectedNames) {
                            succ.put(inj, reqSuccess.get(inj));
                            parm.put(inj, reqParams.get(inj));
                        }
                        g.requireds(new HashSet<>(injectedNames), succ, parm);
                    }
                    for (int i = 0; i < paramTypes.size(); i++) {
                        Type pt = paramTypes.get(i);
                        int s = g.slot(pt);
                        code.aload(1);
                        pushInt(code, i);
                        code.aaload();
                        unbox(code, pt, s);
                        g.bind(params.get(i), s, pt);
                    }
                    for (int i = 0; i < valueNames.size(); i++) {
                        Type ct = valueTypes.get(i);
                        int s = g.slot(ct);
                        code.aload(0);
                        code.getfield(cd, captureField(i), jvmType(ct));
                        store(code, s, ct);
                        g.bind(valueNames.get(i), s, ct);
                    }
                    Type rt = g.genExpr(body);
                    box(code, rt);
                    code.areturn();
                });
            });
        }

        /**
         * Emits {@code e} in tail position: every path ends in an {@code areturn}.
         *
         * <p>Constructing an invariant-bearing data goes through {@code __construct}, which checks the
         * invariant and returns a {@code Result}; {@code ConstraintViolation.orThrow} turns that into
         * either the value (returned) or a thrown {@code ConstraintViolation} — an invariant violation
         * aborts rather than riding an output case (spec 7.3, 9.4).
         * Because a desugared {@code require} (spec 16.4) is an {@code if} whose branches are tail,
         * this is reached for constructions on both sides of a guard — there is no second, unchecked
         * construction path.
         */
        void emitTail(Core e, ClassDesc cdB, Set<String> requiredNames, Map<String, Type> requiredSuccess) {
            emitTail(e, cdB, requiredNames, requiredSuccess, null);
        }

        // {@code expected} is the declared return/output type of the body being emitted (issue #70): it
        // is threaded to a tail-position fold the same way {@link #genExpr} threads it in value
        // position, so a fold over an empty-collection seed materialises its step at the accumulator
        // type the checker pinned rather than a bottom. Null when no declared type is in scope.
        void emitTail(Core e, ClassDesc cdB, Set<String> requiredNames, Map<String, Type> requiredSuccess,
                      Type expected) {
            emitLine(e);
            switch (e) {
                case Core.LetIn li -> {
                    if (li.value() instanceof Core.Call call && requiredNames.contains(call.fn())) {
                        // call an injected required behavior; requiredCall handles both the unary
                        // Behavior contract and a multi-input base (issue #57), leaving the success
                        // value cast on the stack
                        Type letType = call.type();
                        requiredCall(call);
                        int vSlot = slot(letType);
                        store(code, vSlot, letType);
                        bind(li.name(), vSlot, letType);
                    } else {
                        Type vt = li.value().type();
                        if (vt instanceof Type.FnOf fn) {
                            // a lambda chosen at runtime (e.g. by an `if`) — a first-class Fn
                            // (spec §blocks), at the parameter types the checker inferred for it
                            emitFunctionValue(li.value(), fn.params());
                        } else {
                            genExpr(li.value(), vt);
                        }
                        int slot = slot(vt);
                        store(code, slot, vt);
                        bind(li.name(), slot, vt);
                    }
                    emitTail(li.body(), cdB, requiredNames, requiredSuccess, expected);
                }
                case Core.If iff -> {
                    genExpr(iff.cond());
                    Label elseL = code.newLabel();
                    code.ifeq(elseL);
                    emitTail(iff.then(), cdB, requiredNames, requiredSuccess, expected);
                    code.labelBinding(elseL);
                    emitTail(iff.els(), cdB, requiredNames, requiredSuccess, expected);
                }
                case Core.Match m -> emitTailMatch(m, cdB, requiredNames, requiredSuccess, expected);
                case Core.Call call when tcoName != null && call.fn().equals(tcoName)
                        && call.args().size() == tcoParams.size() -> emitSelfTailCall(call);
                case Core.NewData nd when DataChecker.isInvariantBearing(nd.typeName(), symbols) -> {
                    ClassDesc cdType = cd(nd.typeName());
                    Map<String, Type> flds = fieldTypes((Ast.Data) symbols.declaration(nd.typeName()));
                    emitFieldValues(flds, nd.inits(), nd.spreads());
                    emitLine(nd);   // re-pin: a field init may have moved the line off the construction
                    code.invokestatic(cdType, "__construct", MethodTypeDesc.of(CD_Result, fieldDescs(flds)));
                    code.invokestatic(CD_ConstraintViolation, "orThrow", MTD_orThrow);
                    code.areturn();
                }
                default -> {
                    Type rt = genExpr(e, expected);
                    box(code, rt);
                    code.areturn();
                }
            }
        }

        /** Marks the entry of a self-tail-recursive helper. The parameters are already bound to their
         * slots; a later tail-position self-call jumps back here after reassigning them, so the helper
         * loops instead of recursing (see {@link #emitTail} and {@link #emitSelfTailCall}). */
        void beginSelfRecursion(String name, List<Ast.FnParam> params) {
            this.tcoName = name;
            this.tcoParams = params;
            this.tcoEntry = code.newLabel();
            code.labelBinding(tcoEntry);
        }

        /** A tail-position call to the helper being emitted: recompute the arguments — each still reads
         * the current parameter slots — then overwrite the slots and loop. Arguments are pushed
         * left-to-right and stored in reverse so no slot is overwritten before every argument has been
         * read (e.g. {@code loop(acc + n, n - 1)} reads both {@code acc} and {@code n}). */
        private void emitSelfTailCall(Core.Call call) {
            List<Var> params = new ArrayList<>(tcoParams.size());
            for (Ast.FnParam p : tcoParams) {
                params.add(env.get(p.name()));
            }
            for (int i = 0; i < call.args().size(); i++) {
                Type at = genExpr(call.args().get(i));
                Type pt = params.get(i).type();
                if (isReference(pt) && !isReference(at)) {
                    box(code, at);
                }
            }
            for (int i = call.args().size() - 1; i >= 0; i--) {
                store(code, params.get(i).slot(), params.get(i).type());
            }
            code.goto_(tcoEntry);
        }

        /** Pushes each field's value in declaration order: an explicit initializer, else the field
         * carried over from a spread source (ADR-0021). */
        void emitFieldValues(Map<String, Type> fields, List<Core.FieldInit> inits, List<String> spreads) {
            Map<String, Core.FieldInit> byName = new HashMap<>();
            for (Core.FieldInit init : inits) {
                byName.put(init.name(), init);
            }
            for (String field : fields.keySet()) {
                Core.FieldInit init = byName.get(field);
                if (init != null) {
                    // push the field's declared type so a field valued by a fold over an empty seed
                    // materialises its step closure at the field's type (issue #70)
                    genExpr(init.value(), fields.get(field));
                    continue;
                }
                for (String sp : spreads) {
                    Ast.Data src = (Ast.Data) symbols.get(((Type.Ref) varType(sp)).name());
                    if (fieldTypes(src).containsKey(field)) {
                        spreadField(sp, field);
                        break;
                    }
                }
            }
        }

        /** Builds an ArrayList of the literal's elements and returns it immutably. An empty {@code []}
         * adopts a pushed-down list type, as {@code Map.empty}/{@code Set.empty} do and as the checker
         * already does: a written {@code let xs: List<Int> = []} otherwise emits at {@code List<_>},
         * and reading an element back unboxes the bottom (issue #74). */
        private void listLit(Core.ListLit lit) {
            code.new_(CD_ArrayList);
            code.dup();
            code.invokespecial(CD_ArrayList, "<init>", MTD_void);
            for (Core el : lit.elements()) {
                code.dup();
                box(code, genExpr(el));
                code.invokevirtual(CD_ArrayList, "add", MTD_ArrayList_add);
                code.pop();
            }
            code.invokestatic(CD_List, "copyOf", MTD_List_copyOf, true);
        }

        /** Builds a tuple {@code (e1, e2, ...)} as an {@code Object[]}, boxing each element (ADR-0036).
         * A pushed-down tuple type reaches each element, as it does in the checker, so a written
         * {@code (Map<String, Int>, List<String>)} seed materialises at those types (issue #74). */
        private void tuple(Core.Tuple t) {
            pushInt(code, t.elements().size());
            code.anewarray(CD_Object);
            for (int i = 0; i < t.elements().size(); i++) {
                code.dup();
                pushInt(code, i);
                box(code, genExpr(t.elements().get(i)));
                code.aastore();
            }
        }

        /** Reads a tuple element by index: {@code arr[i]}, cast back to the element's type. */
        private void tupleGet(Core.TupleGet tg) {
            genExpr(tg.tuple());
            pushInt(code, tg.index());
            code.aaload();
            castFromObject(code, tg.type());
        }

        /** Binds the bytecode that follows to {@code e}'s source line, for the {@code LineNumberTable}
         * (spec 19.1). Every {@code Core} node keeps its {@code SourcePos}, so a runtime stack trace
         * — an invariant abort above all — points back to the {@code .sou} line. Consecutive nodes on
         * the same line (a subexpression tree, or a tail node re-lined by {@code genExpr}) collapse to
         * one entry. */
        private void emitLine(Core e) {
            int line = e.pos() != null ? e.pos().line() : 0;
            if (line > 0 && line != lastEmittedLine) {
                code.lineNumber(line);
                lastEmittedLine = line;
            }
        }

        /**
         * Emits a Core expression — the single expression emitter (ADR-0021); every node kind is
         * handled here. A {@code let} whose value is a runtime-selected function still asks the
         * type checker (which works on the AST) whether the value is such a function and for its
         * parameter types, so those calls go through {@link Core#toAst()}: Core is untyped and type
         * inference lives in the checker, so the backend reuses it rather than re-deriving types.
         */
        Type genExpr(Core e) {
            return genExpr(e, null);
        }

        /**
         * Emits {@code e} and yields its type: the one the checker decided, read off the node
         * (issue #81). Nothing here derives a type of its own — where a type drives the emission
         * (which instruction, which descriptor, which slot), it is read from the node that carries it.
         *
         * <p>{@code expected} mirrors the checker's bidirectional pass (issue #70): it is pushed into
         * a fold call so codegen materialises the step closure at the same accumulator type the
         * checker validated. Only the passthrough arms (if/let/match/call) forward it.
         */
        Type genExpr(Core e, Type expected) {
            if (e.type() == null) {
                throw new IllegalStateException("this node reached the emitter untyped: "
                        + e.getClass().getSimpleName() + " at " + e.pos());
            }
            emitLine(e);
            switch (e) {
                case Core.Int x -> code.loadConstant(x.value());
                case Core.Decimal x -> {
                    code.new_(CD_BigDecimal);
                    code.dup();
                    code.loadConstant(x.value().toString());
                    code.invokespecial(CD_BigDecimal, "<init>",
                            MethodTypeDesc.of(ConstantDescs.CD_void, CD_String));
                }
                case Core.Str x -> code.loadConstant(x.value());
                case Core.Bool x -> {
                    if (x.value()) code.iconst_1(); else code.iconst_0();
                }
                case Core.Var v -> {
                    Var var = env.get(v.name());
                    if (var != null) {
                        load(code, var.slot(), var.type());
                    } else if (symbols.declaration(v.name()) instanceof Ast.UnitData) {
                        ClassDesc cdU = cd(v.name());
                        code.new_(cdU);
                        code.dup();
                        code.invokespecial(cdU, "<init>", MTD_void);
                    } else {
                        throw new CompileException(v.pos(), "unbound identifier `" + v.name() + "`");
                    }
                }
                case Core.Neg n -> {
                    if (genExpr(n.operand()) == Type.DECIMAL) {
                        code.invokevirtual(CD_BigDecimal, "negate", MethodTypeDesc.of(CD_BigDecimal));
                    } else {
                        code.lneg();               // Int is carried as a long
                    }
                }
                case Core.FieldAccess fa -> {
                    Type targetType = genExpr(fa.target());
                    emitFieldRead(code, ((Type.Ref) targetType).name(), fa.field(), fa.type());
                }
                case Core.If iff -> {
                    genExpr(iff.cond());
                    Label elseL = code.newLabel();
                    Label end = code.newLabel();
                    code.ifeq(elseL);
                    genExpr(iff.then(), expected);
                    code.goto_(end);
                    code.labelBinding(elseL);
                    genExpr(iff.els(), expected);
                    code.labelBinding(end);
                }
                case Core.ListLit lit -> listLit(lit);
                case Core.Tuple t -> tuple(t);
                case Core.TupleGet tg -> tupleGet(tg);
                case Core.Binary bin -> binary(bin);
                case Core.NewData nd -> newData(nd);
                case Core.Match m -> match(m, expected);
                case Core.Call c -> call(c, expected);
                case Core.LetIn li -> {
                    // a `let` outside tail position: bind, then value the body
                    Type vt = li.value().type();
                    if (vt instanceof Type.FnOf fn) {
                        // a lambda chosen at runtime (e.g. by an `if`): a first-class Fn (spec §blocks),
                        // at the parameter types the checker inferred from its applications
                        emitFunctionValue(li.value(), fn.params());
                    } else {
                        genExpr(li.value(), vt);
                    }
                    int s = slot(vt);
                    store(code, s, vt);
                    bind(li.name(), s, vt);
                    genExpr(li.body(), expected);
                }
                // a block has no value of its own; it is inlined by the call it is passed to
                case Core.Block b -> throw new CompileException(b.pos(), "a block is not a value");
            }
            return e.type();
        }

        private void match(Core.Match m, Type expected) {
            Type st = genExpr(m.scrutinee());
            int sSlot = slot(st);
            store(code, sSlot, st);
            Type element = st instanceof Type.OptionOf oo ? oo.element() : null;
            Label end = code.newLabel();
            for (Core.Case c : m.cases()) {
                Label nextCase = code.newLabel();
                // A case binding is scoped to its arm: save any outer binding it shadows and restore it
                // after the arm, or a later arm reusing the name would resolve to this arm's slot.
                Var prevBinding = c.binding() != null ? env.get(c.binding()) : null;
                emitCaseGuard(c, sSlot, st, element, nextCase);
                genExpr(c.body(), expected);
                if (c.binding() != null) {
                    restore(c.binding(), prevBinding);
                }
                code.goto_(end);
                code.labelBinding(nextCase);
            }
            emitMatchFallthrough();
            code.labelBinding(end);
        }

        /** Emits {@code match} in tail position: each arm body is emitted through {@link #emitTail}, so
         * a tail-position self-call inside an arm (as a self-hosted fold makes, matching {@code
         * List.get}) loops rather than recursing. Each arm returns (or tail-loops), so no join label is
         * needed — the next arm's dispatch follows its predecessor's {@code nextCase}. */
        private void emitTailMatch(Core.Match m, ClassDesc cdB, Set<String> requiredNames,
                                   Map<String, Type> requiredSuccess, Type expected) {
            Type st = genExpr(m.scrutinee());
            int sSlot = slot(st);
            store(code, sSlot, st);
            Type element = st instanceof Type.OptionOf oo ? oo.element() : null;
            for (Core.Case c : m.cases()) {
                Label nextCase = code.newLabel();
                // A case binding is scoped to its arm (see {@link #match}): restore any outer binding it
                // shadows before the next arm's dispatch.
                Var prevBinding = c.binding() != null ? env.get(c.binding()) : null;
                emitCaseGuard(c, sSlot, st, element, nextCase);
                emitTail(c.body(), cdB, requiredNames, requiredSuccess, expected);
                if (c.binding() != null) {
                    restore(c.binding(), prevBinding);
                }
                code.labelBinding(nextCase);
            }
            emitMatchFallthrough();
        }

        /** The {@code instanceof} dispatch and case binding for one {@code match} arm; on no match,
         * jumps to {@code nextCase}. Shared by value-position {@link #match} and tail-position
         * {@link #emitTailMatch} so the two stay in step. */
        private void emitCaseGuard(Core.Case c, int sSlot, Type st, Type element, Label nextCase) {
            List<String> cases = c.caseTypes();
            if (element != null) {
                // Option match: a single Some/None case (or-patterns are rejected by the checker)
                String caseName = cases.get(0);
                code.aload(sSlot);
                code.instanceOf(caseName.equals("Some") ? CD_OptionSome : CD_OptionNone);
                code.ifeq(nextCase);
                if (caseName.equals("Some")) {
                    // unwrap Some(v) -> v, bound to the element type
                    code.aload(sSlot);
                    code.checkcast(CD_OptionSome);
                    code.invokevirtual(CD_OptionSome, "value", MTD_Object);
                    int bslot = slot(element);
                    unbox(code, element, bslot);
                    if (c.binding() != null) {
                        bind(c.binding(), bslot, element);
                    }
                }
            } else if (cases.size() == 1) {
                code.aload(sSlot);
                code.instanceOf(matchCaseClass(cases.get(0)));
                code.ifeq(nextCase);
                if (c.binding() != null) {
                    // a data case binds the instance; a primitive case (e.g. Int) unboxes the value
                    Type bt = c.bindType();   // what the checker narrowed the scrutinee to here
                    code.aload(sSlot);
                    int bslot = slot(bt);
                    unbox(code, bt, bslot);
                    bind(c.binding(), bslot, bt);
                }
            } else {
                // or-pattern: run the body if the value is any of the cases; the binding (if any)
                // is the scrutinee's sum type, which every alternative already is
                Label body = code.newLabel();
                for (String caseName : cases) {
                    code.aload(sSlot);
                    code.instanceOf(matchCaseClass(caseName));
                    code.ifne(body);
                }
                code.goto_(nextCase);
                code.labelBinding(body);
                if (c.binding() != null) {
                    bind(c.binding(), sSlot, st);
                }
            }
        }

        /** The unreachable tail of a {@code match}: it is exhaustive by construction (the checker), so
         * falling past every arm throws rather than returning a bogus value. */
        private void emitMatchFallthrough() {
            code.new_(CD_IllegalStateException);
            code.dup();
            code.invokespecial(CD_IllegalStateException, "<init>", MTD_void);
            code.athrow();
        }

        private void newData(Core.NewData nd) {
            Ast.Data owner = (Ast.Data) symbols.declaration(nd.typeName());
            Map<String, Type> flds = fieldTypes(owner);
            ClassDesc cdType = cd(nd.typeName());
            TypeName built = symbols.resolve(nd.typeName());
            // A type of another module is built through its checked entry: `new` reaches a constructor
            // that is not public, and the checked entry is the declared path either way.
            if (DataChecker.isInvariantBearing(built, symbols) || symbols.isForeign(built)) {
                // In value position (a match arm, a non-tail let, a call argument, ...) the checked
                // construction goes through __construct just as it does in tail (see emitTail): the
                // invariant runs and orThrow either yields the value or aborts with a
                // ConstraintViolation. orThrow returns Object, so narrow it back to the value type.
                emitFieldValues(flds, nd.inits(), nd.spreads());
                emitLine(nd);   // re-pin: a field init may have moved the line off the construction
                finishInvariantConstruct(cdType, flds);
                return;
            }
            code.new_(cdType);
            code.dup();
            emitFieldValues(flds, nd.inits(), nd.spreads());
            code.invokespecial(cdType, "<init>",
                    MethodTypeDesc.of(ConstantDescs.CD_void, fieldDescs(flds)));
        }

        /** Emits the checked-construction tail — {@code __construct(fields) -> Result}, {@code orThrow}
         * (yield, or abort on invariant violation), and a narrowing cast — with the field values
         * already on the stack. */
        private void finishInvariantConstruct(ClassDesc cdType, Map<String, Type> flds) {
            code.invokestatic(cdType, "__construct", MethodTypeDesc.of(CD_Result, fieldDescs(flds)));
            code.invokestatic(CD_ConstraintViolation, "orThrow", MTD_orThrow);
            code.checkcast(cdType);
        }

        /** Wraps a base value (Int/Decimal) already on the stack into a single-value newtype, running
         * its invariant check — the closed-arithmetic counterpart of {@link #newData}. An
         * invariant-bearing newtype goes through {@code __construct}/{@code orThrow} (aborts on
         * violation, which a behavior's guard is meant to have discharged); a plain newtype is stashed
         * and built with {@code new}/{@code <init>}. */
        private Type wrapNewtypeValue(TypeName ntName, Type base) {
            Ast.Data owner = (Ast.Data) symbols.get(ntName);
            Map<String, Type> flds = fieldTypes(owner);
            ClassDesc cdType = cd(ntName);
            if (DataChecker.isInvariantBearing(ntName, symbols) || symbols.isForeign(ntName)) {
                finishInvariantConstruct(cdType, flds);
            } else {
                int s = slot(base);
                store(code, s, base);
                code.new_(cdType);
                code.dup();
                load(code, s, base);
                code.invokespecial(cdType, "<init>",
                        MethodTypeDesc.of(ConstantDescs.CD_void, fieldDescs(flds)));
            }
            return Type.ref(ntName);
        }

        Type varType(String name) {
            return env.get(name).type();
        }

        void spreadField(String spreadVar, String field) {
            Var v = env.get(spreadVar);
            TypeName srcName = ((Type.Ref) v.type()).name();
            Ast.Data src = (Ast.Data) symbols.get(srcName);
            load(code, v.slot(), v.type());
            emitFieldRead(code, srcName, field, fieldTypes(src).get(field));
        }

        // --- the surface Intrinsics drives to emit a shipped primitive (ADR-0028) ---

        /** Boxes an {@code Int}/{@code Bool} on the stack for an erased ({@code Object}) runtime slot;
         * a no-op for a reference, which is already an {@code Object}. */
        void emitBox(Type type) {
            box(code, type);
        }

        void emitInvokeStatic(ClassDesc owner, String method, MethodTypeDesc desc) {
            code.invokestatic(owner, method, desc);
        }

        void emitInvokeVirtual(ClassDesc owner, String method, MethodTypeDesc desc) {
            code.invokevirtual(owner, method, desc);
        }

        /** Narrows an {@code Int} (a {@code long}) to a JVM {@code int}, for a JDK method taking an
         * {@code int} index. */
        void emitL2i() {
            code.l2i();
        }

        private void call(Core.Call call, Type expected) {
            Prelude.IntrinsicSig intrinsic = Prelude.intrinsics().get(call.fn());
            if (intrinsic != null) {
                Intrinsics.emit(this, intrinsic.key(), call);
                return;
            }
            switch (call.fn()) {
                case "String.length" -> {
                    genExpr(call.args().get(0));
                    code.invokevirtual(CD_String, "length", MethodTypeDesc.of(ConstantDescs.CD_int));
                    code.i2l();
                }
                case "String.toInt" -> {
                    // Strings.toInt returns a boxed Long or NotANumber.INSTANCE — the Int | NotANumber
                    // union, carried as Object (like intDivide's DivisionByZero result).
                    genExpr(call.args().get(0));
                    code.invokestatic(CD_Strings, "toInt", MethodTypeDesc.of(CD_Object, CD_String));
                }
                case "String.toDecimal" -> {
                    // the sibling of toInt: a boxed BigDecimal or NotANumber.INSTANCE, carried as Object
                    genExpr(call.args().get(0));
                    code.invokestatic(CD_Strings, "toDecimal", MethodTypeDesc.of(CD_Object, CD_String));
                }
                case "List.length" -> {
                    genExpr(call.args().get(0));
                    code.invokeinterface(CD_List, "size", MTD_size);
                    code.i2l();
                }
                case "List.get" -> {
                    genExpr(call.args().get(1));      // get(index, xs): list then index (Lists.get)
                    genExpr(call.args().get(0));      // long index
                    code.invokestatic(CD_Lists, "get",
                            MethodTypeDesc.of(CD_Option, CD_List, ConstantDescs.CD_long));
                }
                case "List.max", "List.min" -> {
                    genExpr(call.args().get(0));
                    code.invokestatic(CD_Lists, bareOp(call.fn()),   // "max" / "min"
                            MethodTypeDesc.of(CD_Option, CD_List));
                }
                case "List.find", "List.sortBy" -> {
                    // find(p, xs) / sortBy(key, xs): the function is a value here (not inlined into a
                    // fold), so materialise it as an Fn, then pass the list. The list's element type
                    // gives the function's one parameter type.
                    Type elem = ((Type.ListOf) call.args().get(1).type()).element();
                    emitFunctionValue(call.args().get(0), List.of(elem));   // Fn on the stack
                    genExpr(call.args().get(1));                            // then the List
                    if (call.fn().equals("List.find")) {
                        code.invokestatic(CD_Lists, "find", MethodTypeDesc.of(CD_Option, CD_Fn, CD_List));
                    } else {
                        code.invokestatic(CD_Lists, "sortBy", MethodTypeDesc.of(CD_List, CD_Fn, CD_List));
                    }
                }
                case "Option.map" -> {
                    // map(f, opt): materialise f as an Fn (its one parameter is the option's element
                    // type), then the option. `Option` is not surface-writable, so the rewrap into
                    // Some(f v) / None happens in the runtime kernel (Option.map), not in emitted code.
                    Type elem = ((Type.OptionOf) call.args().get(1).type()).element();
                    emitFunctionValue(call.args().get(0), List.of(elem));   // Fn on the stack
                    genExpr(call.args().get(1));                            // then the Option
                    code.invokestatic(CD_Options, "map", MethodTypeDesc.of(CD_Option, CD_Fn, CD_Option));
                }
                case "Map.get" -> {
                    genExpr(call.args().get(1));      // get(key, m): map then key (Maps.get)
                    genExpr(call.args().get(0));      // key (a reference)
                    code.invokestatic(CD_Maps, "get",
                            MethodTypeDesc.of(CD_Option, CD_Map, ConstantDescs.CD_Object));
                }
                case "Map.empty" -> code.invokestatic(CD_Maps, "empty", MethodTypeDesc.of(CD_Map));
                case "Set.empty" -> code.invokestatic(CD_Sets, "empty", MethodTypeDesc.of(CD_Set));
                case "Date", "DateTime" -> {
                    // a written date: the checker has already parsed the literal, so the text is
                    // known good and this is a plain parse of a constant string.
                    ClassDesc cd = call.fn().equals("Date") ? CD_LocalDate : CD_LocalDateTime;
                    code.loadConstant(((Core.Str) call.args().get(0)).value());
                    code.invokestatic(cd, "parse", MethodTypeDesc.of(cd, CD_CharSequence));
                }
                case "Int.divide", "Decimal.divide" -> {
                    if (call.args().size() == 4) {
                        decimalDivide(call);
                    } else {
                        intDivide(call, true);
                    }
                }
                case "Int.remainder" -> intDivide(call, false);
                case "Decimal.toInt" -> decimalToInt(call);
                case "Decimal.round" -> decimalRound(call);
                default -> {
                    Var fv = env.get(call.fn());
                    if (fv != null && fv.type() instanceof Type.FnOf fnType) {
                        applyFn(call, fnType);
                    } else if (ctx.recursiveHelpers.containsKey(call.fn())) {
                        recursiveHelperCall(call);
                    } else if (reqNames.contains(call.fn())) {
                        requiredCall(call);
                    } else {
                        throw new CompileException(call.pos(), "unknown function `" + call.fn() + "`");
                    }
                }
            }
        }

        /** Calls a recursive helper as a static method on {@code $Fns} (spec 13.1): each argument is
         * evaluated and boxed, the {@code invokestatic} returns {@code Object}, and the result is cast
         * back to the helper's declared return type. A self- or mutual call reaches here the same way.
         * A function parameter is passed as a first-class {@code Fn} value (a closure): the argument
         * block is materialised rather than evaluated as a plain value, and an {@code Fn} is already a
         * reference, so it fits the {@code Object} slot without boxing. */
        private void recursiveHelperCall(Core.Call call) {
            // The checker resolved this call's type variables when it typed it — the accumulator a
            // fold's step runs at, the result the caller casts to — and left the decision on the
            // nodes, so nothing is resolved a second time here (issue #81).
            for (Core arg : call.args()) {
                if (arg.type() instanceof Type.FnOf fn) {
                    if (stepNeverRuns(fn)) {
                        code.aconst_null();
                    } else {
                        emitFunctionValue(arg, fn.params());
                    }
                } else {
                    box(code, genExpr(arg));
                }
            }
            invokeRecursiveHelper(call);
            castFromObject(code, call.type());
        }

        /**
         * Whether a step closure would never be applied: one of its parameters is the bare bottom, so
         * it is the element of an empty-literal list and there are no elements — {@code foldFrom} over
         * {@code []} yields the seed. Such a step is passed as a null {@code Fn} rather than
         * materialised, since materialising it would unbox the bottom element (as {@code acc + x}
         * does with {@code x}) and crash. An empty *seed* (a {@code List<Nothing>} accumulator) is a
         * reference and still materialises.
         */
        private static boolean stepNeverRuns(Type.FnOf fn) {
            for (Type p : fn.params()) {
                if (p instanceof Type.Nothing) {
                    return true;
                }
            }
            return false;
        }

        private void invokeRecursiveHelper(Core.Call call) {
            ClassDesc[] params = new ClassDesc[call.args().size()];
            java.util.Arrays.fill(params, CD_Object);
            code.invokestatic(ClassDesc.of(pkg + ".$Fns"), CodegenContext.recursiveHelperMethod(call.fn()),
                    MethodTypeDesc.of(CD_Object, params));
        }

        /** The operation name from a qualified builtin call ({@code "List.max"} → {@code "max"}). */
        private static String bareOp(String fn) {
            int dot = fn.indexOf('.');
            return dot < 0 ? fn : fn.substring(dot + 1);
        }

        /** {@code divide}/{@code remainder} on Int: a zero divisor takes the DivisionByZero case,
         * otherwise the quotient/remainder is boxed (spec 18.2). */
        private void intDivide(Core.Call call, boolean divide) {
            genExpr(call.args().get(0));
            int aSlot = slot(Type.INT);
            code.lstore(aSlot);
            genExpr(call.args().get(1));
            int bSlot = slot(Type.INT);
            code.lstore(bSlot);
            code.lload(bSlot);
            code.lconst_0();
            code.lcmp();
            Label zero = code.newLabel();
            Label end = code.newLabel();
            code.ifeq(zero);                       // b == 0 -> DivisionByZero case
            code.lload(aSlot);
            code.lload(bSlot);
            if (divide) {
                code.ldiv();
            } else {
                code.lrem();
            }
            code.invokestatic(CD_Long, "valueOf", MTD_Long_valueOf);   // box the quotient
            code.goto_(end);
            code.labelBinding(zero);
            code.getstatic(CD_DivisionByZero, "INSTANCE", CD_DivisionByZero);
            code.labelBinding(end);
        }

        /** {@code divide(a, b, scale, mode)} on Decimal: a zero divisor takes the DivisionByZero
         * case, otherwise {@code a.divide(b, scale, RoundingMode.mode)} (spec 18.3). */
        private void decimalDivide(Core.Call call) {
            genExpr(call.args().get(0));
            int aSlot = slot(Type.DECIMAL);
            code.astore(aSlot);
            genExpr(call.args().get(1));
            int bSlot = slot(Type.DECIMAL);
            code.astore(bSlot);
            code.aload(bSlot);
            code.invokevirtual(CD_BigDecimal, "signum", MethodTypeDesc.of(ConstantDescs.CD_int));
            Label zero = code.newLabel();
            Label end = code.newLabel();
            code.ifeq(zero);                       // signum == 0 -> DivisionByZero case
            code.aload(aSlot);
            code.aload(bSlot);
            genExpr(call.args().get(2));              // scale (Int, a long)
            code.l2i();
            String mode = ((Core.Var) call.args().get(3)).name();
            code.getstatic(CD_RoundingMode, mode, CD_RoundingMode);
            code.invokevirtual(CD_BigDecimal, "divide", MTD_bdDivide);
            code.goto_(end);
            code.labelBinding(zero);
            code.getstatic(CD_DivisionByZero, "INSTANCE", CD_DivisionByZero);
            code.labelBinding(end);
        }

        /** {@code toInt(d, mode)}: the whole number `d` rounds to under `mode`, which is written at
         * the call as `divide`'s is. The kernel aborts on a value too large for an Int. */
        private void decimalToInt(Core.Call call) {
            genExpr(call.args().get(0));
            String mode = ((Core.Var) call.args().get(1)).name();
            code.getstatic(CD_RoundingMode, mode, CD_RoundingMode);
            code.invokestatic(CD_DecimalMath, "toInt",
                    MethodTypeDesc.of(ConstantDescs.CD_long, CD_BigDecimal, CD_RoundingMode));
        }

        /** {@code round(d, scale, mode)}: `d` at the given number of decimal places, the mode written
         * at the call as `toInt`'s and `divide`'s are. Unlike `toInt` the result stays a Decimal, so
         * this is a plain {@code BigDecimal.setScale} and needs no kernel. */
        private void decimalRound(Core.Call call) {
            genExpr(call.args().get(0));
            genExpr(call.args().get(1));   // scale (Int, a long)
            code.l2i();
            String mode = ((Core.Var) call.args().get(2)).name();
            code.getstatic(CD_RoundingMode, mode, CD_RoundingMode);
            code.invokevirtual(CD_BigDecimal, "setScale",
                    MethodTypeDesc.of(CD_BigDecimal, ConstantDescs.CD_int, CD_RoundingMode));
        }

        /** Emits an inline call to an injected required behavior, leaving its success value on
         * the stack cast to the success type (spec 12.2, 13). */
        private void requiredCall(Core.Call call) {
            Type success = reqSuccess.get(call.fn());
            if (ctx.isMultiArgRequired(call.fn())) {
                // 2+ inputs: the required behavior is its own base class, called with a typed
                // invokevirtual apply(A,B,…); each arg is left as its declared param type (issue #57)
                MethodTypeDesc desc = ctx.requiredApplyDesc(call.fn());
                code.aload(0);
                code.getfield(cdName, call.fn(), ctx.cdBehavior(call.fn()));
                for (Core arg : call.args()) {
                    Type at = genExpr(arg);
                    box(code, at);   // a primitive boxes to its apply-param type; a reference already matches
                }
                code.invokevirtual(ctx.cdBehavior(call.fn()), "apply", desc);
                stackCast(success);
                return;
            }
            code.aload(0);
            code.getfield(cdName, call.fn(), CD_Behavior);
            if (call.args().isEmpty()) {
                code.aconst_null();        // `() -> R`: the implementation ignores the input
            } else {
                Type at = genExpr(call.args().get(0));
                box(code, at);
            }
            code.invokeinterface(CD_Behavior, "apply", MTD_apply);
            stackCast(success);
        }

        /** Casts the {@code Object} on the stack to {@code type}, unboxing primitives. */
        private void stackCast(Type type) {
            if (type == Type.INT) {
                code.checkcast(CD_Long);
                code.invokevirtual(CD_Long, "longValue", MethodTypeDesc.of(ConstantDescs.CD_long));
            } else if (type == Type.BOOL) {
                code.checkcast(CD_Boolean);
                code.invokevirtual(CD_Boolean, "booleanValue", MethodTypeDesc.of(ConstantDescs.CD_boolean));
            } else if (!(type instanceof Type.Union)) {
                code.checkcast(jvmType(type));
            }
        }

        private void binary(Core.Binary bin) {
            switch (bin.op()) {
                case AND -> {
                    genExpr(bin.left());
                    genExpr(bin.right());
                    code.iand();
                }
                case OR -> {
                    genExpr(bin.left());
                    genExpr(bin.right());
                    code.ior();
                }
                // `+ - * /` work on two Int or two Decimal operands (spec 18.1). Int aborts on
                // overflow, and `/` aborts on a zero divisor; Decimal does not overflow, and its `/`
                // rounds by the default scale/mode. Case handling for a zero divisor is the
                // divide/remainder functions, not the operator.
                case ADD, SUB, MUL, DIV -> {
                    // Newtype arithmetic (closed `+`/`-`, or scalar `*`/`/` by a plain number) opens
                    // each operand to its base, computes on the base, then re-wraps the result into the
                    // newtype (re-checking its invariant). A non-newtype operand (a scalar) is left as
                    // is — unwrapNewtypeValue is a no-op. `closedNewtypeArithResult` returns null when
                    // neither operand is a newtype (plain base arithmetic), leaving the value unwrapped.
                    Type lraw = genExpr(bin.left());
                    Type t = unwrapNewtypeValue(lraw);
                    Type rraw = genExpr(bin.right());
                    unwrapNewtypeValue(rraw);
                    if (t == Type.DECIMAL) {
                        switch (bin.op()) {
                            case ADD -> code.invokevirtual(CD_BigDecimal, "add", MTD_bdArith);
                            case SUB -> code.invokevirtual(CD_BigDecimal, "subtract", MTD_bdArith);
                            case MUL -> code.invokevirtual(CD_BigDecimal, "multiply", MTD_bdArith);
                            default  -> code.invokestatic(CD_DecimalMath, "divide", MTD_bdDivideOp);
                        }
                    } else {
                        String m = switch (bin.op()) {
                            case ADD -> "addExact";
                            case SUB -> "subtractExact";
                            case MUL -> "multiplyExact";
                            default  -> "divideExact";
                        };
                        code.invokestatic(CD_IntMath, m, MTD_intExact);
                    }
                    // Closed `+`/`-` and scalar `*`/`/` stay in the newtype: when the checker typed
                    // this expression as one, re-wrap the base value it left on the stack.
                    if (bin.type() instanceof Type.Ref ref) {
                        wrapNewtypeValue(ref.name(), t);
                    }
                }
                case CONCAT -> {
                    Type lt = genExpr(bin.left());
                    // `++` over two strings is Elm's appendable on String; the checker guarantees both
                    // sides are String here, so emit `a.concat(b)` rather than the list join.
                    if (lt == Type.STRING) {
                        genExpr(bin.right());
                        code.invokevirtual(CD_String, "concat",
                                MethodTypeDesc.of(CD_String, CD_String));
                    } else if (bin.right() instanceof Core.ListLit lit && lit.elements().size() == 1) {
                        // `acc ++ [x]` is how every fold-derived combinator grows its list
                        // (souther.list's map/filter), so it runs once per element. Push the element
                        // itself: building a one-element list for `concat` to immediately take apart
                        // costs an ArrayList, a copyOf, and an iterator on the hot path.
                        box(code, genExpr(lit.elements().get(0)));
                        code.invokestatic(CD_Lists, "append", MTD_Lists_append);
                    } else {
                        genExpr(bin.right());
                        code.invokestatic(CD_Lists, "concat", MTD_Lists_concat);
                    }
                }
                default -> {
                    // A single-value newtype compares by its underlying value: open each operand to
                    // that value right after it is pushed, then the primitive comparison below applies
                    // (金額 <= 金額, 金額 <= 100 — the checker allows only same newtype or a bare literal).
                    Type lt = unwrapNewtypeValue(genExpr(bin.left()));
                    unwrapNewtypeValue(genExpr(bin.right()));
                    boolean ordering = switch (bin.op()) {
                        case LT, LE, GT, GE -> true;
                        default -> false;
                    };
                    if (ordering && (lt == Type.STRING || lt == Type.DECIMAL
                            || lt == Type.DATE || lt == Type.DATETIME)) {
                        // String, Decimal, Date, DateTime all carry as Comparable — String,
                        // BigDecimal, LocalDate, LocalDateTime — so one compareTo reduces the order
                        // to its sign against 0. BigDecimal.compareTo ignores scale, which matches
                        // Decimal equality (spec 7.1); the others order lexicographically / in time.
                        code.invokeinterface(CD_Comparable, "compareTo", MTD_compareTo_Object);
                        code.iconst_0();
                        comparisonMaterialize(bin.op(), false);
                        return;
                    }
                    if (lt == Type.STRING) {
                        code.invokevirtual(CD_String, "equals",
                                MethodTypeDesc.of(ConstantDescs.CD_boolean, CD_Object));
                        if (bin.op() == Ast.BinOp.NE) {
                            code.iconst_1();
                            code.ixor();
                        }
                        return;
                    }
                    if (lt == Type.DECIMAL) {
                        emitDecimalEquals(code);          // by value, ignoring scale (spec 7.1)
                        if (bin.op() == Ast.BinOp.NE) {
                            code.iconst_1();
                            code.ixor();
                        }
                        return;
                    }
                    if (isReference(lt)) {
                        // a data (or any boxed value) compares by its fields — the generated
                        // equals (spec 7.1). Objects.equals keeps it null-tolerant.
                        code.invokestatic(CD_Objects, "equals", MTD_Objects_equals);
                        if (bin.op() == Ast.BinOp.NE) {
                            code.iconst_1();
                            code.ixor();
                        }
                        return;
                    }
                    comparisonMaterialize(bin.op(), lt == Type.INT);
                }
            }
        }

        private void comparisonMaterialize(Ast.BinOp op, boolean isLong) {
            Label t = code.newLabel();
            Label end = code.newLabel();
            if (isLong) {
                code.lcmp();
                switch (op) {
                    case LT -> code.iflt(t);
                    case LE -> code.ifle(t);
                    case GT -> code.ifgt(t);
                    case GE -> code.ifge(t);
                    case EQ -> code.ifeq(t);
                    case NE -> code.ifne(t);
                    default -> throw new IllegalStateException();
                }
            } else {
                switch (op) {
                    case LT -> code.if_icmplt(t);
                    case LE -> code.if_icmple(t);
                    case GT -> code.if_icmpgt(t);
                    case GE -> code.if_icmpge(t);
                    case EQ -> code.if_icmpeq(t);
                    case NE -> code.if_icmpne(t);
                    default -> throw new IllegalStateException();
                }
            }
            code.iconst_0();
            code.goto_(end);
            code.labelBinding(t);
            code.iconst_1();
            code.labelBinding(end);
        }

        /** A name-to-type view of this scope, for the checker's inference helpers. */
        private Map<String, Type> typesEnv() {
            Map<String, Type> t = new HashMap<>();
            env.forEach((k, v) -> t.put(k, v.type()));
            return t;
        }

        /** {@link #typesEnv} plus the recursive helpers' signatures, so re-typing an expression that
         * calls one (a nested {@code foldFrom} in a fold's seed) resolves it as a function. */
        private Map<String, Type> typesEnvWithHelpers() {
            Map<String, Type> t = typesEnv();
            ctx.recursiveHelpers.forEach((name, h) -> {
                if (t.containsKey(name)) {
                    return;   // a local of the same name shadows the helper, as it does in the checker
                }
                List<Type> params = new ArrayList<>();
                for (Ast.FnParam p : h.params()) {
                    params.add(TypeOps.resolveParamType(p.type(), symbols));
                }
                t.put(name, Type.fn(params, successType(h.declaredReturn())));
            });
            return t;
        }

        /** Emits a function value from its elaborated node: the parameter and result types are the
         * ones the checker decided, so nothing is inferred here (issue #81). */
        private void emitFunctionValue(Core value, List<Type> paramTypes) {
            switch (value) {
                case Core.Block b -> emitLambda(b, paramTypes);
                case Core.If iff -> {
                    genExpr(iff.cond());
                    Label elseL = code.newLabel();
                    Label end = code.newLabel();
                    code.ifeq(elseL);
                    emitFunctionValue(iff.then(), paramTypes);
                    code.goto_(end);
                    code.labelBinding(elseL);
                    emitFunctionValue(iff.els(), paramTypes);
                    code.labelBinding(end);
                }
                case Core.LetIn li -> {
                    // a capture binding around the function: bind it here so the lambda captures it
                    Type vt = genExpr(li.value());
                    int s = slot(vt);
                    store(code, s, vt);
                    bind(li.name(), s, vt);
                    emitFunctionValue(li.body(), paramTypes);
                }
                default -> genExpr(value);
            }
        }

        /** Compiles a lambda to a synthetic {@code Fn} class and emits {@code new} of it, passing the
         * captured free variables (and any injected behaviors it calls) to its constructor. Its
         * parameter and result types are the ones the checker put on the block (issue #81). */
        private void emitLambda(Core.Block block, List<Type> paramTypes) {
            emitLambda(block.params(), block.body(), paramTypes,
                    ((Type.FnOf) block.type()).result(), freeVars(block));
        }

        private void emitLambda(List<String> params, Core body, List<Type> paramTypes,
                                Type resultType, List<String> free) {
            List<String> valueNames = new ArrayList<>();
            List<Type> valueTypes = new ArrayList<>();
            List<String> injectedNames = new ArrayList<>();
            for (String c : free) {
                if (env.containsKey(c)) {
                    valueNames.add(c);
                    valueTypes.add(env.get(c).type());
                } else {
                    injectedNames.add(c);   // an injected behavior the closure calls (spec 13.2)
                }
            }
            String className = pkg + ".$Fn" + ctx.nextLambdaId();
            ClassDesc cd = ClassDesc.of(className);
            ctx.addSynth(className, generateLambdaClass(cd, params, body, paramTypes, resultType,
                    valueNames, valueTypes, injectedNames, reqSuccess, reqParams));

            code.new_(cd);
            code.dup();
            List<ClassDesc> ctorDescs = new ArrayList<>();
            for (int i = 0; i < valueNames.size(); i++) {
                load(code, env.get(valueNames.get(i)).slot(), valueTypes.get(i));
                ctorDescs.add(jvmType(valueTypes.get(i)));
            }
            for (String inj : injectedNames) {
                code.aload(0);                              // the enclosing behavior instance
                code.getfield(cdName, inj, ctx.requiredFieldType(inj));    // its injected field
                ctorDescs.add(ctx.requiredFieldType(inj));
            }
            code.invokespecial(cd, "<init>",
                    MethodTypeDesc.of(ConstantDescs.CD_void, ctorDescs.toArray(new ClassDesc[0])));
        }

        /** Applies a first-class function value: {@code f.apply(new Object[]{args...})}, then casts
         * the {@code Object} result back to the function's result type. */
        private void applyFn(Core.Call call, Type.FnOf fnType) {
            Var fv = env.get(call.fn());
            load(code, fv.slot(), fv.type());   // the Fn receiver
            pushInt(code, call.args().size());
            code.anewarray(CD_Object);
            for (int i = 0; i < call.args().size(); i++) {
                code.dup();
                pushInt(code, i);
                Type at = genExpr(call.args().get(i));
                box(code, at);
                code.aastore();
            }
            code.invokeinterface(CD_Fn, "apply", MTD_Fn_apply);
            stackCast(fnType.result());   // Object result -> the function's result type
        }

        /** The free variables of a lambda: names its body reads that are bound in the enclosing
         * scope (so must be captured), in first-seen order. */
        private List<String> freeVars(Core.Block block) {
            LinkedHashSet<String> free = new LinkedHashSet<>();
            collectFree(block.body(), new HashSet<>(block.params()), free);
            return new ArrayList<>(free);
        }

        private void collectFree(Core e, Set<String> bound, LinkedHashSet<String> free) {
            switch (e) {
                case Core.Var v -> maybeFree(v.name(), bound, free);
                case Core.Call c -> {
                    maybeFree(c.fn(), bound, free);   // an applied function value is captured too
                    c.args().forEach(a -> collectFree(a, bound, free));
                }
                case Core.FieldAccess fa -> collectFree(fa.target(), bound, free);
                case Core.Binary bin -> {
                    collectFree(bin.left(), bound, free);
                    collectFree(bin.right(), bound, free);
                }
                case Core.Neg neg -> collectFree(neg.operand(), bound, free);
                case Core.NewData nd -> {
                    nd.inits().forEach(i -> collectFree(i.value(), bound, free));
                    nd.spreads().forEach(sp -> maybeFree(sp, bound, free));
                }
                case Core.If iff -> {
                    collectFree(iff.cond(), bound, free);
                    collectFree(iff.then(), bound, free);
                    collectFree(iff.els(), bound, free);
                }
                case Core.LetIn li -> {
                    collectFree(li.value(), bound, free);
                    Set<String> inner = new HashSet<>(bound);
                    inner.add(li.name());
                    collectFree(li.body(), inner, free);
                }
                case Core.Match m -> {
                    collectFree(m.scrutinee(), bound, free);
                    for (Core.Case c : m.cases()) {
                        Set<String> inner = bound;
                        if (c.binding() != null) {
                            inner = new HashSet<>(bound);
                            inner.add(c.binding());
                        }
                        collectFree(c.body(), inner, free);
                    }
                }
                case Core.Block b -> {
                    Set<String> inner = new HashSet<>(bound);
                    inner.addAll(b.params());
                    collectFree(b.body(), inner, free);
                }
                case Core.ListLit lit -> lit.elements().forEach(x -> collectFree(x, bound, free));
                case Core.Tuple tup -> tup.elements().forEach(x -> collectFree(x, bound, free));
                case Core.TupleGet tg -> collectFree(tg.tuple(), bound, free);
                case Core.Int _ -> { }
                case Core.Decimal _ -> { }
                case Core.Str _ -> { }
                case Core.Bool _ -> { }
            }
        }

        private void maybeFree(String name, Set<String> bound, LinkedHashSet<String> free) {
            if (!bound.contains(name) && (env.containsKey(name) || reqNames.contains(name))) {
                free.add(name);
            }
        }

    private record Var(int slot, Type type) {}
}
