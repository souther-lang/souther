package souther.compiler.codegen;

import souther.compiler.check.Scope;
import souther.compiler.check.Symbols;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.check.CheckContext;
import souther.compiler.check.Elaborator;
import souther.compiler.check.DataChecker;
import souther.compiler.check.Lower;
import souther.compiler.check.ReqSig;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.check.TypeOps;
import souther.compiler.check.MatchElaborator;
import souther.compiler.core.Core;
import souther.compiler.core.GrowingFold;

import java.lang.classfile.ClassFile;
import java.lang.classfile.CodeBuilder;
import java.lang.classfile.Label;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.MethodTypeDesc;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;

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

    private ClassDesc cd(TypeName typeName) {
        return ctx.cd(typeName);
    }

    private ClassDesc matchCaseClass(TypeName caseName) {
        return ctx.matchCaseClass(caseName);
    }

    private Map<String, Type> fieldTypes(Ast.Data data) {
        return ctx.fieldTypes(data);
    }

    /** The fields a construction spread copies from a value of {@code src}: a data's own, or the part
     * every case of a sum spreads, which the sum's sealed interface declares as accessors. */
    private Map<String, Type> spreadableFields(TypeName src) {
        return symbols.get(src) instanceof Ast.SumData sum
                ? TypeOps.commonSpreadFields(sum, symbols)
                : fieldTypes((Ast.Data) symbols.get(src));
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
        /**
         * Where each binding this body holds lives.
         *
         * <p>Keyed by the binding rather than by its spelling, so an inner binding of the same
         * spelling takes a slot of its own and leaves the outer one where it was. Nothing has to be
         * put back when a scope ends, which is what a name-keyed table needed and did not always do.
         */
        private final Map<BindingId, Var> locals = new HashMap<>();
        /** Where each injected behavior a lambda captured lives. Declared rather than bound, so it is
         * reached by the name it is declared under. */
        private final Map<String, Var> captured = new HashMap<>();
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
        /** Members of this body's declared output union that reach it through a bridge case; empty
         * for every other body. @see #injectsInto */
        private List<TypeName> injectMembers = List.of();

        BodyGen(CodegenContext ctx, CodeBuilder code, Ast.Data data, ClassDesc cdName, int firstSlot) {
            this.ctx = ctx;
            this.pkg = ctx.pkg;
            this.symbols = ctx.symbols;
            this.code = code;
            this.data = data;
            this.cdName = cdName;
            this.nextSlot = firstSlot;
        }

        /**
         * Makes this body the implementation of a behavior whose declared output is a union, so its
         * returns leave the union's JVM representation rather than a bare Souther value.
         *
         * <p>Inside a body every value is a Souther value. It becomes a member of the result union at
         * the return, and a caller turns it back at the call. The two conversions are the only places
         * the two forms meet — nothing in between ever holds a bridge case, so no return can wrap one
         * a second time.
         */
        void injectsInto(Type out) {
            this.injectMembers = ctx.bridgedMembers(out);
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

        void bind(Ast.Binder binder, int slot, Type type) {
            bind(binder.id(), binder.name(), slot, type);
        }

        void bind(BindingId binding, String name, int slot, Type type) {
            put(locals, binding, new Var(slot, type, name));
        }

        /** Where an injected behavior a lambda captured was put. */
        void bindCaptured(String injected, int slot, Type type) {
            put(captured, injected, new Var(slot, type, injected));
        }

        private <K> void put(Map<K, Var> where, K key, Var var) {
            where.put(key, var);
            nextSlot = Math.max(nextSlot, var.slot() + width(var.type()));
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
            return Elaborator.elaborate(Lower.desugarExpr(e), scope(),
                    new CheckContext(symbols, data, reqSigs()), expected);
        }

        /**
         * Reads a field onto the stack through the data's accessor. A data is a record, so its backing
         * field is private and the accessor is the read — for a data of this module as much as for an
         * imported one, whose field is out of reach across the module = package boundary anyway
         * (spec 8.5, 19.2).
         */
        private void emitFieldRead(CodeBuilder code, TypeName ownerName, String field, Type ft) {
            MethodTypeDesc mtd = MethodTypeDesc.of(jvmType(ft));
            if (symbols.get(ownerName) instanceof Ast.SumData) {
                // a field every case spreads is declared on the sum's sealed interface (issue #160)
                code.invokeinterface(cd(ownerName), field, mtd);
            } else {
                code.invokevirtual(cd(ownerName), field, mtd);
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
        private byte[] generateLambdaClass(ClassDesc cd, List<Ast.Binder> params, Core body,
                                           List<Type> paramTypes,
                                           Type resultType, List<Core.Read> captures,
                                           List<String> injectedNames, Map<String, Type> reqSuccess,
                                           Map<String, List<Type>> reqParams) {
            return build(cd, cb -> {
                cb.withFlags(ClassFile.ACC_FINAL | ClassFile.ACC_SUPER);
                cb.withInterfaceSymbols(CD_Fn);
                for (int i = 0; i < captures.size(); i++) {
                    cb.withField(captureField(i), jvmType(captures.get(i).type()),
                            ClassFile.ACC_PRIVATE | ClassFile.ACC_FINAL);
                }
                for (String inj : injectedNames) {   // named after the behavior so requiredCall reads it
                    cb.withField(inj, ctx.requiredFieldType(inj), ClassFile.ACC_PRIVATE | ClassFile.ACC_FINAL);
                }
                List<ClassDesc> ctor = new ArrayList<>();
                for (Core.Read c : captures) {
                    ctor.add(jvmType(c.type()));
                }
                for (String inj : injectedNames) {
                    ctor.add(ctx.requiredFieldType(inj));
                }
                cb.withMethodBody("<init>", MethodTypeDesc.of(ConstantDescs.CD_void, ctor.toArray(new ClassDesc[0])),
                        ClassFile.ACC_PUBLIC, code -> {
                    code.aload(0);
                    code.invokespecial(CD_Object, "<init>", MTD_void);
                    int slot = 1;
                    for (int i = 0; i < captures.size(); i++) {
                        Type ct = captures.get(i).type();
                        code.aload(0);
                        load(code, slot, ct);
                        code.putfield(cd, captureField(i), jvmType(ct));
                        slot += width(ct);
                    }
                    for (String inj : injectedNames) {
                        code.aload(0);
                        code.aload(slot);
                        code.putfield(cd, inj, ctx.requiredFieldType(inj));
                        slot += 1;
                    }
                    code.return_();
                });
                if (captures.isEmpty() && injectedNames.isEmpty()) {
                    // Captures are this class's only fields, so capturing nothing makes it stateless
                    // and one instance per lambda site is enough. Two sites never share one, and
                    // Souther has no function equality, so this is unobservable. Package-private:
                    // every use site is in the module's own package.
                    emitSharedInstance(cb, cd, 0, null);
                }
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
                    for (int i = 0; i < captures.size(); i++) {
                        Core.Read c = captures.get(i);
                        int s = g.slot(c.type());
                        code.aload(0);
                        code.getfield(cd, captureField(i), jvmType(c.type()));
                        store(code, s, c.type());
                        g.bind(c.binding(), c.name(), s, c.type());
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
         * Because a desugared {@code guard} (spec 16.4) is an {@code if} whose branches are tail,
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
                        bind(li.binder(), vSlot, letType);
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
                        bind(li.binder(), slot, vt);
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
                // Both branches stay in tail position, so a self-recursive helper guarded by an
                // attempt loops exactly as one guarded by a plain condition does. Falling through to
                // the value emitter would leave the recursive call a real call and grow the stack.
                case Core.IfConstructed ic -> {
                    Attempt a = emitAttempt(ic);
                    bind(ic.binder(), a.slot(), ic.construct().type());
                    emitTail(ic.then(), cdB, requiredNames, requiredSuccess, expected);
                    code.labelBinding(a.elseLabel());
                    // Each departure is in tail position too, so it returns on its own and needs no
                    // jump past the ones emitted after it.
                    emitDepartures(ic, a,
                            body -> emitTail(body, cdB, requiredNames, requiredSuccess, expected),
                            null);
                }
                case Core.Match m -> emitTailMatch(m, cdB, requiredNames, requiredSuccess, expected);
                case Core.Call call when tcoName != null && call.fn().equals(tcoName)
                        && call.args().size() == tcoParams.size() -> emitSelfTailCall(call);
                case Core.NewData nd when DataChecker.isInvariantBearing(nd.typeName(), symbols) -> {
                    ClassDesc cdType = cd(nd.typeName());
                    Map<String, Type> flds = fieldTypes((Ast.Data) symbols.get(nd.typeName()));
                    emitFieldValues(flds, nd.inits(), nd.spreads());
                    emitLine(nd);   // re-pin: a field init may have moved the line off the construction
                    code.invokestatic(cdType, "__construct", MethodTypeDesc.of(CD_Result, fieldDescs(flds)));
                    code.invokestatic(CD_ConstraintViolation, "orThrow", MTD_orThrow);
                    returnValue();
                }
                default -> {
                    Type rt = genExpr(e, expected);
                    box(code, rt);
                    returnValue();
                }
            }
        }

        /**
         * Returns the Souther value on the stack as a member of the declared output union: a member
         * this module declared is the member itself, any other is put into its bridge case. The
         * dispatch runs over the union's members, which are known here, so nothing is guessed from
         * the value alone.
         */
        private void returnValue() {
            ResultBoundary.inject(code, ctx, injectMembers, slot(Type.NOTHING));
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
                params.add(locals.get(p.binder().id()));
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
        void emitFieldValues(Map<String, Type> fields, List<Core.FieldInit> inits,
                             List<Core.Read> spreads) {
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
                for (Core.Read sp : spreads) {
                    if (spreadableFields(((Type.Ref) varType(sp)).name()).containsKey(field)) {
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
                if (el.type() instanceof Type.FnOf fn) {
                    // a function held in a list is a value like any other, so it is materialised as
                    // an Fn here rather than expanded into a call site it does not have
                    emitFunctionValue(el, fn.params());
                } else {
                    box(code, genExpr(el));
                }
                code.invokevirtual(CD_ArrayList, "add", MTD_ArrayList_add);
                code.pop();
            }
            code.invokestatic(CD_List, "copyOf", MTD_List_copyOf, true);
        }

        /** Builds a tuple {@code (e1, e2, ...)}, boxing each element (ADR-0036). The elements go into
         * an array and the array is handed to {@code Tuple.of}, which takes ownership of it: it was
         * built one instruction earlier and nothing else holds it. A pushed-down tuple type reaches
         * each element, as it does in the checker, so a written {@code (Map<String, Int>,
         * List<String>)} seed materialises at those types (issue #74). */
        private void tuple(Core.Tuple t) {
            if (t.elements().size() == 2) {
                // the arity every fold-carried tuple has: built outright, with no array between
                code.new_(CD_TuplePair);
                code.dup();
                box(code, genExpr(t.elements().get(0)));
                box(code, genExpr(t.elements().get(1)));
                code.invokespecial(CD_TuplePair, "<init>", MTD_TuplePair_init);
                return;
            }
            pushInt(code, t.elements().size());
            code.anewarray(CD_Object);
            for (int i = 0; i < t.elements().size(); i++) {
                code.dup();
                pushInt(code, i);
                box(code, genExpr(t.elements().get(i)));
                code.aastore();
            }
            code.invokestatic(CD_Tuple, "ofOwned", MTD_Tuple_ofOwned, true);
        }

        /** Reads a tuple element by index, cast back to the element's type. */
        private void tupleGet(Core.TupleGet tg) {
            genExpr(tg.tuple());
            if (tg.tuple().type() instanceof Type.TupleOf tu && tu.elements().size() == 2) {
                code.getfield(CD_TuplePair, tg.index() == 0 ? "first" : "second", CD_Object);
            } else {
                pushInt(code, tg.index());
                code.invokeinterface(CD_Tuple, "get", MTD_Tuple_get);
            }
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
                case Core.Read v -> {
                    Var var = locals.get(v.binding());
                    if (var == null) {
                        throw new CompileException(v.pos(), "unbound identifier `" + v.name() + "`");
                    }
                    load(code, var.slot(), var.type());
                }
                // a unit type has exactly one value, and naming it is that value (spec §unit-data).
                // Which unit is on the node: a body expanded in from another module's published
                // helper names that module's unit, which this module need not declare at all — and,
                // if it declares one spelled the same, is not the same unit.
                case Core.UnitValue u -> loadSharedInstance(code, cd(u.data()));
                case Core.Builtin b -> throw new IllegalStateException(
                        "`" + b.name() + "` is read by the operation that takes it, not emitted, at "
                                + b.pos());
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
                    Type want = shapeOf(iff, expected);
                    code.ifeq(elseL);
                    genExpr(iff.then(), want);
                    code.goto_(end);
                    code.labelBinding(elseL);
                    genExpr(iff.els(), want);
                    code.labelBinding(end);
                }
                case Core.IfConstructed ic -> {
                    Attempt a = emitAttempt(ic);
                    Label end = code.newLabel();
                    bind(ic.binder(), a.slot(), ic.construct().type());
                    genExpr(ic.then(), shapeOf(ic, expected));
                    code.goto_(end);

                    code.labelBinding(a.elseLabel());
                    emitDepartures(ic, a, body -> genExpr(body, shapeOf(ic, expected)), end);
                    code.labelBinding(end);
                }
                case Core.OptionSome s -> {
                    // `Option.some` takes the value as an Object, so a primitive element boxes here
                    // the way a list element does.
                    genExpr(s.value());
                    JvmTypes.box(code, s.value().type());
                    code.invokestatic(CD_Option, "some",
                            MethodTypeDesc.of(CD_Option, ConstantDescs.CD_Object), true);
                }
                case Core.OptionNone _ ->
                        code.invokestatic(CD_Option, "none", MethodTypeDesc.of(CD_Option), true);
                case Core.Unreachable u -> unreachable(u, expected);
                case Core.ListLit lit -> listLit(lit);
                case Core.Tuple t -> tuple(t);
                case Core.TupleGet tg -> tupleGet(tg);
                case Core.Binary bin -> binary(bin);
                case Core.NewData nd -> newData(nd);
                case Core.Match m -> match(m, expected);
                case Core.Call c -> call(c, expected);
                case Core.Apply a -> applyFn(a, (Type.FnOf) a.fn().type());
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
                    bind(li.binder(), s, vt);
                    genExpr(li.body(), expected);
                }
                // a block has no value of its own; it is inlined by the call it is passed to
                case Core.Block b -> throw new CompileException(b.pos(), "a block is not a value");
            }
            // `unreachable` is typed Never, and what is on the stack is the shape the position asked
            // for, so that is what the caller is told is there.
            if (e instanceof Core.Unreachable && expected != null && !(expected instanceof Type.Never)) {
                return expected;
            }
            return e.type();
        }

        /** The type the branches of {@code e} leave on the stack: what the position asked for, or —
         * where it asked for nothing — the one the checker joined the branches at. A branch that
         * answers {@code unreachable} has no type of its own to merge with the others, so it takes
         * this one. */
        private Type shapeOf(Core e, Type expected) {
            return expected != null ? expected : e.type();
        }

        /**
         * {@code unreachable "reason"}: the abort, and the shape the position it stands in holds.
         *
         * <p>The abort is a call rather than an {@code athrow} so that the arm leaves a value where
         * its siblings leave one, and the code around it verifies as any other arm's does. The shape
         * is what the position asked for, or what the checker recorded when it asked for nothing;
         * neither leaves one where {@code Never} survives to here, and that position is refused
         * rather than emitted.
         */
        private void unreachable(Core.Unreachable u, Type expected) {
            Type shape = expected != null ? expected : u.type();
            if (shape instanceof Type.Never) {
                throw CompileException.of(
                        Diagnostic.of("E1307", "check.unreachable.untyped")
                                .title("check.type.mismatch.title")
                                .at(u.pos(), "unreachable".length())
                                .hint("check.unreachable.untyped.hint").build(),
                        "nothing here says what this position holds, and `unreachable` answers no"
                                + " value to say it with");
            }
            code.loadConstant(abortMessage(u));
            code.invokestatic(CD_UnreachableReached, "reached", MTD_reached);
            stackCast(shape);
        }

        /**
         * What the abort says: the reason the model wrote, and the line and column it wrote it at.
         *
         * <p>No file name. This compiler is not given one — a generated class's {@code SourceFile}
         * is derived from its module name rather than threaded down from a path — and deriving one
         * here would name a file that need not exist, and would name the reading module's when the
         * {@code unreachable} came in with an inlined helper of another. A reader at run time has
         * the frame's own file and line; a reader of E1911 has the row's place beside this one.
         */
        private String abortMessage(Core.Unreachable u) {
            return u.pos() == null ? u.reason() : u.reason() + " (" + u.pos() + ")";
        }

        private void match(Core.Match m, Type expected) {
            Type st = genExpr(m.scrutinee());
            int sSlot = slot(st);
            store(code, sSlot, st);
            Type element = st instanceof Type.OptionOf oo ? oo.element() : null;
            Label end = code.newLabel();
            Type want = shapeOf(m, expected);
            for (Core.Case c : m.cases()) {
                Label nextCase = code.newLabel();
                // A case binding is scoped to its arm: save any outer binding it shadows and restore it
                // after the arm, or a later arm reusing the name would resolve to this arm's slot.

                emitCaseGuard(c, sSlot, st, element, nextCase);
                genExpr(c.body(), want);
                if (c.binding() != null) {
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

                emitCaseGuard(c, sSlot, st, element, nextCase);
                emitTail(c.body(), cdB, requiredNames, requiredSuccess, expected);
                if (c.binding() != null) {
                }
                code.labelBinding(nextCase);
            }
            emitMatchFallthrough();
        }

        /** The {@code instanceof} dispatch and case binding for one {@code match} arm; on no match,
         * jumps to {@code nextCase}. Shared by value-position {@link #match} and tail-position
         * {@link #emitTailMatch} so the two stay in step. */
        private void emitCaseGuard(Core.Case c, int sSlot, Type st, Type element, Label nextCase) {
            List<TypeName> cases = c.caseTypes();
            if (element != null) {
                // Option match: a single Some/None case (or-patterns are rejected by the checker)
                boolean isSome = cases.get(0).name().equals("Some");
                code.aload(sSlot);
                code.instanceOf(isSome ? CD_OptionSome : CD_OptionNone);
                code.ifeq(nextCase);
                if (isSome) {
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
                for (TypeName caseName : cases) {
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
            Ast.Data owner = (Ast.Data) symbols.get(nd.typeName());
            Map<String, Type> flds = fieldTypes(owner);
            ClassDesc cdType = cd(nd.typeName());
            TypeName built = nd.typeName();
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
            MethodTypeDesc ctor = MethodTypeDesc.of(ConstantDescs.CD_void, fieldDescs(flds));
            if (!walksInside(nd)) {
                code.new_(cdType);
                code.dup();
                emitFieldValues(flds, nd.inits(), nd.spreads());
                code.invokespecial(cdType, "<init>", ctor);
                return;
            }
            // A field built by a walk is built through a loop, and a value under construction may not
            // be live across a backwards branch: the reference `new` leaves is uninitialised until
            // `<init>`, and the verifier will not carry one over a jump. So the fields are built first
            // and held in slots, exactly as a newtype's single field already is, and the construction
            // itself is the straight line at the end.
            emitFieldValues(flds, nd.inits(), nd.spreads());
            List<Type> fieldTypes = new ArrayList<>(flds.values());
            int[] held = new int[fieldTypes.size()];
            for (int i = fieldTypes.size() - 1; i >= 0; i--) {
                held[i] = slot(fieldTypes.get(i));
                store(code, held[i], fieldTypes.get(i));
            }
            code.new_(cdType);
            code.dup();
            for (int i = 0; i < fieldTypes.size(); i++) {
                load(code, held[i], fieldTypes.get(i));
            }
            code.invokespecial(cdType, "<init>", ctor);
        }

        /** Whether emitting {@code e} emits a loop — a fold, or the walk a fold that grows a collection
         *  became. What it decides is whether a value being constructed can stay on the stack while its
         *  fields are built. */
        private static boolean walksInside(Core e) {
            if (e instanceof Core.Call c && (c.fn().equals(FOLD)
                    || c.fn().equals(GrowingFold.BUILD) || c.fn().equals(GrowingFold.MAP_BUILD))) {
                return true;
            }
            boolean[] found = {false};
            Core.mapChildren(e, child -> {
                found[0] |= walksInside(child);
                return child;
            });
            return found[0];
        }

        /** Where an attempt's failing side continues, and the slot holding the value its success side
         * names. The binder is the caller's to scope, because how far the success branch reaches
         * differs between value and tail position. */
        private record Attempt(Label elseLabel, int slot, int resultSlot) {}

        /**
         * Emits an attempted construction up to its branch: the same {@code __construct} a plain
         * construction calls, with the {@code Result} branched on rather than handed to
         * {@code ConstraintViolation.orThrow}. The success value is left in the returned slot and the
         * Err side jumps to the returned label; the caller emits the two branches, which is where
         * value position and tail position part company.
         */
        private Attempt emitAttempt(Core.IfConstructed ic) {
            Core.NewData nd = ic.construct();
            Map<String, Type> flds = fieldTypes((Ast.Data) symbols.get(nd.typeName()));
            ClassDesc cdType = cd(nd.typeName());
            emitFieldValues(flds, nd.inits(), nd.spreads());
            emitLine(ic);   // re-pin: a field init may have moved the line off the construction
            code.invokestatic(cdType, "__construct", MethodTypeDesc.of(CD_Result, fieldDescs(flds)));

            int rSlot = slot(Type.STRING);   // a reference slot, as the codecs take for the same Result
            code.astore(rSlot);
            code.aload(rSlot);
            code.instanceOf(CD_ResultErr);
            Label elseL = code.newLabel();
            code.ifne(elseL);

            int bound = slot(nd.type());
            code.aload(rSlot);
            code.checkcast(CD_ResultOk);
            code.invokevirtual(CD_ResultOk, "value", MTD_Object);
            code.checkcast(cdType);
            store(code, bound, nd.type());
            return new Attempt(elseL, bound, rSlot);
        }

        /**
         * Emits an attempt's departures at its else label. One departure naming no clause is the whole
         * of it — any failure is that value. Several are a lookup on the clause the {@code Result}
         * carries: the arms are compared in turn and one is left to fall through, so nothing is emitted
         * for the case where no clause matches. The checker has established there is none — every named
         * clause has an arm, and {@code | _ ->} is there exactly when clauses carry no name.
         *
         * <p>{@code end} is where a departure jumps once its value is built, or null in tail position,
         * where each departure returns instead.
         */
        private void emitDepartures(Core.IfConstructed ic, Attempt a, Consumer<Core> emit, Label end) {
            List<Core.ElseArm> arms = ic.els();
            if (arms.size() == 1 && arms.get(0).clause().isEmpty()) {
                emit.accept(arms.get(0).body());
                return;
            }
            code.aload(a.resultSlot());
            code.checkcast(CD_ResultErr);
            code.invokevirtual(CD_ResultErr, "error", MTD_Object);
            code.checkcast(CD_InvariantFailure);
            code.invokevirtual(CD_InvariantFailure, "clause", MTD_failureClause);
            int cSlot = slot(Type.STRING);
            code.astore(cSlot);
            // One arm is left to fall through, so it needs no comparison: the `| _ ->` where there is
            // one, and otherwise the last arm — with every clause named and answered, a failure that
            // matched none of the others is that one.
            int fallthrough = arms.size() - 1;
            for (int i = 0; i < arms.size(); i++) {
                if (arms.get(i).clause().isEmpty()) {
                    fallthrough = i;
                }
            }
            List<Label> labels = new ArrayList<>();
            for (int i = 0; i < arms.size(); i++) {
                if (i == fallthrough) {
                    labels.add(null);
                    continue;
                }
                Label armL = code.newLabel();
                labels.add(armL);
                // The clause is null for a rule declared without a name, so the constant is the
                // receiver of the comparison and the read value the argument.
                code.loadConstant(arms.get(i).clause().get());
                code.aload(cSlot);
                code.invokevirtual(CD_String, "equals", MTD_equalsObject);
                code.ifne(armL);
            }
            emit.accept(arms.get(fallthrough).body());
            for (int i = 0; i < arms.size(); i++) {
                if (i == fallthrough) {
                    continue;
                }
                if (end != null) {
                    code.goto_(end);
                }
                code.labelBinding(labels.get(i));
                emit.accept(arms.get(i).body());
            }
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

        Type varType(Core.Read read) {
            return locals.get(read.binding()).type();
        }

        void spreadField(Core.Read spreadVar, String field) {
            Var v = locals.get(spreadVar.binding());
            TypeName srcName = ((Type.Ref) v.type()).name();
            load(code, v.slot(), v.type());
            emitFieldRead(code, srcName, field, spreadableFields(srcName).get(field));
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
            // An enumeration's order lives on its sum, so the sort family takes it as a comparator
            // rather than reading a Comparable off the value (issue #161).
            if (call.fn().equals("List.sort")) {
                TypeName ordering = elementOrdering(call.args().get(0));
                if (ordering != null) {
                    code.invokestatic(cd(ordering), ORDERING_METHOD, MTD_ordering, true);
                    genExpr(call.args().get(0));
                    code.invokestatic(CD_Lists, "sort",
                            MethodTypeDesc.of(CD_List, CD_Comparator, CD_List));
                    return;
                }
            }
            Prelude.IntrinsicSig intrinsic = Prelude.intrinsics().get(call.fn());
            if (intrinsic != null) {
                Intrinsics.emit(this, intrinsic.key(), call);
                return;
            }
            switch (call.fn()) {
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
                case "List.max", "List.min" -> {
                    TypeName ordering = elementOrdering(call.args().get(0));
                    if (ordering != null) {
                        code.invokestatic(cd(ordering), ORDERING_METHOD, MTD_ordering, true);
                    }
                    genExpr(call.args().get(0));
                    code.invokestatic(CD_Lists, bareOp(call.fn()),   // "max" / "min"
                            ordering == null
                                    ? MethodTypeDesc.of(CD_Option, CD_List)
                                    : MethodTypeDesc.of(CD_Option, CD_Comparator, CD_List));
                }
                case "List.find", "List.sortBy" -> {
                    // find(p, xs) / sortBy(key, xs): the function is a value here (not inlined into a
                    // fold), so materialise it as an Fn, then pass the list. The list's element type
                    // gives the function's one parameter type.
                    Type elem = ((Type.ListOf) call.args().get(1).type()).element();
                    TypeName ordering = call.fn().equals("List.sortBy")
                            && call.args().get(0).type() instanceof Type.FnOf key
                            ? TypeOps.orderingEnumeration(key.result(), symbols) : null;
                    if (ordering != null) {
                        code.invokestatic(cd(ordering), ORDERING_METHOD, MTD_ordering, true);
                    }
                    emitFunctionValue(call.args().get(0), List.of(elem));   // Fn on the stack
                    genExpr(call.args().get(1));                            // then the List
                    if (call.fn().equals("List.find")) {
                        code.invokestatic(CD_Lists, "find", MethodTypeDesc.of(CD_Option, CD_Fn, CD_List));
                    } else {
                        code.invokestatic(CD_Lists, "sortBy", ordering == null
                                ? MethodTypeDesc.of(CD_List, CD_Fn, CD_List)
                                : MethodTypeDesc.of(CD_List, CD_Comparator, CD_Fn, CD_List));
                    }
                }
                case GrowingFold.BUILD -> buildList(call);
                case GrowingFold.GROW -> growList(call);
                case GrowingFold.MAP_BUILD -> buildMap(call);
                case GrowingFold.PUT -> putIntoMap(call);
                case "Option.map" -> {
                    // map(f, opt): materialise f as an Fn (its one parameter is the option's element
                    // type), then the option. `Option` is not surface-writable, so the rewrap into
                    // Some(f v) / None happens in the runtime kernel (Option.map), not in emitted code.
                    Type elem = ((Type.OptionOf) call.args().get(1).type()).element();
                    emitFunctionValue(call.args().get(0), List.of(elem));   // Fn on the stack
                    genExpr(call.args().get(1));                            // then the Option
                    code.invokestatic(CD_Options, "map", MethodTypeDesc.of(CD_Option, CD_Fn, CD_Option));
                }
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
                    // an injected behavior a lambda captured arrives in a slot rather than in a
                    // field of the enclosing behavior, and is applied as the value it is. This asks
                    // where the value is, not what the name means: what it means was settled when
                    // the call was elaborated, and an injected behavior is not a binding.
                    Var behavior = captured.get(call.fn());
                    if (behavior != null && behavior.type() instanceof Type.FnOf fnType) {
                        applyCaptured(call, fnType);
                    } else if (ctx.emittedHelpers.containsKey(call.fn())) {
                        // The one loop the language has is emitted where it stands, not called.
                        if (!call.fn().equals(FOLD) || !folded(call)) {
                            recursiveHelperCall(call);
                        }
                    } else if (reqNames.contains(call.fn())) {
                        requiredCall(call);
                    } else if (ctx.calleeSig(call.fn()) != null) {
                        behaviorCall(call);
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
                        code.getstatic(CD_Fn, "NEVER", CD_Fn);
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
         * A fold that only grows a list: the walk carries a builder and seals it at the end
         * ({@code GrowingFold}). The step is materialised as it is for the fold this was rewritten
         * from — an empty list still hands over {@code Fn.NEVER} — and the seed is gone, because the
         * builder is the seed.
         */
        private void buildList(Core.Call call) {
            if (walked(call, CD_Lists, MTD_Lists_builder, MTD_Lists_sealed)) {
                return;
            }
            emitStep(call.args().get(0));
            genExpr(call.args().get(1));      // the list walked
            genExpr(call.args().get(2));      // the index walked from (a long)
            code.invokestatic(CD_Lists, "build", MTD_Lists_build);
        }

        /**
         * {@code acc ++ …} inside such a walk: the accumulator is the builder, so this adds to it
         * rather than building a new vector. As with {@code ++} itself, a one-element list literal on
         * the right pushes its element instead of the list around it.
         */
        private void growList(Core.Call call) {
            genExpr(call.args().get(0));
            Core added = call.args().get(1);
            if (added instanceof Core.ListLit lit && lit.elements().size() == 1) {
                box(code, genExpr(lit.elements().get(0)));
                code.invokestatic(CD_Lists, "grow", MTD_Lists_grow);
            } else {
                genExpr(added);
                code.invokestatic(CD_Lists, "growAll", MTD_Lists_growAll);
            }
        }

        /** The same walk for a fold accumulating a map: the builder is the seed and the map it built
         *  is handed over at the end. */
        private void buildMap(Core.Call call) {
            if (walked(call, CD_Maps, MTD_Maps_builder, MTD_Maps_sealed)) {
                return;
            }
            emitStep(call.args().get(0));
            genExpr(call.args().get(1));      // the list walked
            genExpr(call.args().get(2));      // the index walked from (a long)
            code.invokestatic(CD_Maps, "build", MTD_Maps_build);
        }

        /**
         * A fold as the loop it is: the seed in a local, the list walked by its iterator, and the
         * step's own body as the loop body reading the accumulator and the element from locals.
         * Answers whether it was emitted that way — a walk that starts past the head, or whose step
         * is one that never runs, is left to the {@code foldFrom} method (spec 13.1).
         *
         * <p>This is what makes a fold cost what a loop costs, and {@code fold} is the one loop the
         * language has, so it is the whole of what a program's loops cost. Handed to a method instead,
         * the step has to be a first-class {@code Fn}: a class of its own, an {@code Object[]} of
         * boxed arguments per element, an accumulator that is boxed because {@code apply} answers with
         * an {@code Object} — and, where the method walks for every fold in the program, a call site
         * seeing so many different steps that it stops being inlined at all. Emitted here, the step's
         * body reads the locals it closes over directly, an {@code Int} accumulator stays a
         * {@code long} in its slot, and each walk is straight-line code the JIT sees on its own.
         */
        private boolean folded(Core.Call call) {
            if (!(call.args().get(3) instanceof Core.Int from) || from.value() != 0) {
                return false;
            }
            Core seed = call.args().get(1);
            return walked(call.args().get(0), call.args().get(2), () -> {
                Type produced = genExpr(seed);
                asAccumulator(produced, accumulatorOf(call.args().get(0)));
            }, () -> { });
        }

        /** The same walk, accumulating into a builder that is sealed at the end (see
         *  {@link GrowingFold}): the seed is the builder, and the list or map it built is what the
         *  walk answers with. */
        private boolean walked(Core.Call call, ClassDesc helpers,
                               MethodTypeDesc builder, MethodTypeDesc sealed) {
            return walked(call.args().get(0), call.args().get(1),
                    () -> code.invokestatic(helpers, "builder", builder),
                    () -> code.invokestatic(helpers, "sealed", sealed));
        }

        /** The accumulator's type, as the checker put it on the step. */
        private static Type accumulatorOf(Core step) {
            return ((Type.FnOf) step.type()).params().get(0);
        }

        /** Leaves the value on the stack in the accumulator's own form: boxed where the accumulator is
         *  a reference, and left as it is where the accumulator is an {@code Int} or a {@code Bool},
         *  which stays in its slot as a primitive for the length of the walk. */
        private void asAccumulator(Type produced, Type accType) {
            if (accType != Type.INT && accType != Type.BOOL) {
                box(code, produced);
            }
        }

        private boolean walked(Core stepValue, Core walked, Runnable seed, Runnable answer) {
            if (!(stepValue instanceof Core.Block step)
                    || !(step.type() instanceof Type.FnOf fn) || stepNeverRuns(fn)) {
                return false;
            }
            Type accType = fn.params().get(0);
            Type elementType = fn.params().get(1);

            int iterator = slot(Type.STRING);   // a reference slot; the type is not read back
            genExpr(walked);
            code.invokeinterface(CD_List, "iterator", MTD_iterator);
            code.astore(iterator);

            int acc = slot(accType);
            seed.run();
            store(code, acc, accType);

            // The step's body is emitted here rather than in a class of its own, so the names it binds
            // would otherwise stay bound after the walk — and a step that destructures its accumulator
            // binds ordinary names (`let (i, ys) = acc`), which are the caller's names as often as not.
            // The whole scope is put back, the slots it took staying taken.
            Map<BindingId, Var> enclosing = new HashMap<>(locals);
            bind(step.params().get(0), acc, accType);
            int element = slot(elementType);
            bind(step.params().get(1), element, elementType);

            Label next = code.newLabel();
            Label done = code.newLabel();
            code.labelBinding(next);
            code.aload(iterator);
            code.invokeinterface(CD_Iterator, "hasNext", MTD_hasNext);
            code.ifeq(done);
            code.aload(iterator);
            code.invokeinterface(CD_Iterator, "next", MTD_next);
            unbox(code, elementType, element);
            Type stepped = genExpr(step.body());   // the accumulator the step answers with
            asAccumulator(stepped, accType);
            store(code, acc, accType);
            code.goto_(next);
            code.labelBinding(done);

            locals.clear();
            locals.putAll(enclosing);
            load(code, acc, accType);
            answer.run();
            return true;
        }

        /** {@code Map.insert(key, value, acc)} inside such a walk: a write into the builder. */
        private void putIntoMap(Core.Call call) {
            genExpr(call.args().get(0));
            box(code, genExpr(call.args().get(1)));
            box(code, genExpr(call.args().get(2)));
            code.invokestatic(CD_Maps, "put", MTD_Maps_put);
        }

        /** The step of a build, as the fold it was rewritten from would have materialised it — an
         *  empty list still hands over {@code Fn.NEVER}. */
        private void emitStep(Core step) {
            if (step.type() instanceof Type.FnOf fn && !stepNeverRuns(fn)) {
                emitFunctionValue(step, fn.params());
            } else {
                code.getstatic(CD_Fn, "NEVER", CD_Fn);
            }
        }

        /**
         * Whether a step closure would never be applied: one of its parameters is the bare bottom, so
         * it is the element of an empty-literal list and there are no elements — {@code foldFrom} over
         * {@code []} yields the seed. Such a step is passed as {@link souther.runtime.Fn#NEVER} rather
         * than materialised, since materialising it would unbox the bottom element (as {@code acc + x}
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
            code.invokestatic(ClassDesc.of(pkg + ".$Fns"), CodegenContext.helperMethod(call.fn()),
                    MethodTypeDesc.of(CD_Object, params));
        }

        /** The self-hosted walk of {@code souther.list}: a recursive helper everywhere else, and the
         *  loop every fold in a program is, which is why the emitter knows its name. */
        private static final String FOLD = "List.foldFrom";

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
            String mode = ((Core.Builtin) call.args().get(3)).name();
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
            String mode = ((Core.Builtin) call.args().get(1)).name();
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
            String mode = ((Core.Builtin) call.args().get(2)).name();
            code.getstatic(CD_RoundingMode, mode, CD_RoundingMode);
            code.invokevirtual(CD_BigDecimal, "setScale",
                    MethodTypeDesc.of(CD_BigDecimal, ConstantDescs.CD_int, CD_RoundingMode));
        }

        /** Emits an inline call to an injected required behavior, leaving its success value on
         * the stack cast to the success type (spec 12.2, 13). */
        /**
         * Calls a behavior that depends on nothing (spec {@code [#calling-a-behavior]}). It is built
         * here rather than read out of a field: with an empty requirement set there is nothing to
         * inject, so its {@code $Impl} has a no-argument constructor. This is the same sequence a
         * {@code >->} stage already emits for a behavior it builds, and it reaches an imported one
         * the same way, because {@link CodegenContext#cdBehaviorImpl} resolves the declaring
         * module's package.
         *
         * <p>A single-input behavior's interface extends {@code Behavior}, so the erased
         * {@code apply} links; one with any other arity declares a typed {@code apply} of its own.
         */
        private void behaviorCall(Core.Call call) {
            ReqSig sig = ctx.calleeSig(call.fn());
            ClassDesc impl = ctx.cdBehaviorImpl(call.fn());
            code.new_(impl);
            code.dup();
            code.invokespecial(impl, "<init>", MTD_void);
            if (sig.params().size() == 1) {
                Type at = genExpr(call.args().get(0));
                box(code, at);
                code.invokeinterface(CD_Behavior, "apply", MTD_apply);
                project(call.fn(), sig.success());
                stackCast(sig.success());
                return;
            }
            for (Core arg : call.args()) {
                Type at = genExpr(arg);
                box(code, at);
            }
            code.invokeinterface(ctx.cdBehavior(call.fn()), "apply",
                    ctx.typedApplyDesc(call.fn(), sig.params(), sig.success()));
            project(call.fn(), sig.success());
            stackCast(sig.success());
        }

        private void requiredCall(Core.Call call) {
            Type success = reqSuccess.get(call.fn());
            if (ctx.isStandaloneRequired(call.fn())) {
                // other than one input: the required behavior is its own base class, called with a
                // typed invokevirtual apply(A,B,…); each arg is left as its declared param type
                // (issue #57). A `() -> R` produces, so the call hands it nothing.
                MethodTypeDesc desc = ctx.requiredApplyDesc(call.fn());
                code.aload(0);
                code.getfield(cdName, call.fn(), ctx.cdBehavior(call.fn()));
                for (Core arg : call.args()) {
                    Type at = genExpr(arg);
                    box(code, at);   // a primitive boxes to its apply-param type; a reference already matches
                }
                code.invokevirtual(ctx.cdBehavior(call.fn()), "apply", desc);
                project(call.fn(), success);
                stackCast(success);
                return;
            }
            code.aload(0);
            code.getfield(cdName, call.fn(), CD_Behavior);
            Type at = genExpr(call.args().get(0));
            box(code, at);
            code.invokeinterface(CD_Behavior, "apply", MTD_apply);
            project(call.fn(), success);
            stackCast(success);
        }

        /**
         * Turns the result of a behavior call back into a Souther value: a member the callee's module
         * declared arrives as itself, one that reached the union through a bridge case has its value
         * taken out. Runs over the callee's union members, which are known at the call, so the value
         * is never asked whether it happens to be wrapped.
         *
         * <p>Done at the call rather than at the {@code match} arm that reads it, because not every
         * result is matched: a body may answer with a call's result directly, and the bridge cases of
         * the callee's module are not members of this module's union. Projected here, the value is a
         * Souther value again and this behavior's own return puts it into its own bridge case.
         */
        private void project(String callee, Type calleeOut) {
            List<TypeName> bridged = ctx.bridgedMembersOf(callee, calleeOut);
            ResultBoundary.project(code, ctx, callee, bridged, slot(Type.NOTHING));
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
                    // An enumeration compares by where its case stands in the declaration, which the
                    // sum answers for both operands — `stage < Won` pairs a sum with one of its cases.
                    TypeName enumOf = orderingOf(bin);
                    if (enumOf != null) {
                        genExpr(bin.left());
                        code.invokestatic(cd(enumOf), ORDER_METHOD, MTD_order, true);
                        genExpr(bin.right());
                        code.invokestatic(cd(enumOf), ORDER_METHOD, MTD_order, true);
                        comparisonMaterialize(bin.op(), false);
                        return;
                    }
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
                    if (isReference(lt)) {
                        // What sameness is, is the runtime's to say: a data compares by its fields,
                        // an amount ignores its scale, a collection asks that of what it holds
                        // (spec 7.1). A pair of Decimals takes the overload for them.
                        emitValueEquals(code, lt == Type.DECIMAL);
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

        /** The enumeration a {@code <}/{@code <=}/{@code >}/{@code >=} orders its operands by, or
         * null when this is not that comparison. */
        private TypeName orderingOf(Core.Binary bin) {
            boolean ordering = switch (bin.op()) {
                case LT, LE, GT, GE -> true;
                default -> false;
            };
            return ordering
                    ? TypeOps.comparisonEnumeration(bin.left().type(), bin.right().type(), symbols)
                    : null;
        }

        /** The enumeration a list's elements are ordered by, or null when they are ordered otherwise
         * (an ordered primitive or a newtype over one, which carry their own {@code Comparable}). */
        private TypeName elementOrdering(Core arg) {
            return arg.type() instanceof Type.ListOf lo
                    ? TypeOps.orderingEnumeration(lo.element(), symbols) : null;
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

        /** What the body may name here: the bindings this emitter holds, and the injected behaviors
         * a lambda captured, which a call reaches by the name they are declared under. */
        private Scope bound() {
            Map<BindingId, Scope.Binding> held = new LinkedHashMap<>();
            locals.forEach((binding, v) -> held.put(binding, new Scope.Binding(v.name(), v.type())));
            Map<String, Type> declared = new HashMap<>();
            captured.forEach((name, v) -> declared.put(name, v.type()));
            return Scope.of(held).reaching(declared);
        }

        /** {@link #bound} plus the recursive helpers' signatures, so re-typing an expression that
         * calls one (a nested {@code foldFrom} in a fold's seed) resolves it as a function. Only a
         * recursive helper's signature can be read here, and a recursive helper declares its return
         * type (spec 13.1); an example-applied helper is emitted beside them without declaring one, and
         * no standing call names it — it is expanded wherever a body calls it. */
        private Scope scope() {
            Scope held = bound();
            Map<String, Type> declared = new HashMap<>(held.declared());
            ctx.emittedHelpers.forEach((name, h) -> {
                if (declared.containsKey(name) || h.declaredReturn() == null) {
                    return;
                }
                List<Type> params = new ArrayList<>();
                for (Ast.FnParam p : h.params()) {
                    params.add(TypeOps.resolveParamType(p.type(), symbols));
                }
                declared.put(name, Type.fn(params, successType(h.declaredReturn())));
            });
            return held.reaching(declared);
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
                    bind(li.binder(), s, vt);
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

        private void emitLambda(List<Ast.Binder> params, Core body, List<Type> paramTypes,
                                Type resultType, Reaches free) {
            List<Core.Read> captures = free.bindings();
            List<String> injectedNames = free.injected();
            String className = pkg + ".$Fn" + ctx.nextLambdaId();
            ClassDesc cd = ClassDesc.of(className);
            ctx.addSynth(className, generateLambdaClass(cd, params, body, paramTypes, resultType,
                    captures, injectedNames, reqSuccess, reqParams));

            // the same condition generateLambdaClass interned on — it must stay the same one
            if (captures.isEmpty() && injectedNames.isEmpty()) {
                loadSharedInstance(code, cd);
                return;
            }

            code.new_(cd);
            code.dup();
            List<ClassDesc> ctorDescs = new ArrayList<>();
            for (Core.Read c : captures) {
                load(code, locals.get(c.binding()).slot(), c.type());
                ctorDescs.add(jvmType(c.type()));
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
        private void applyFn(Core.Apply call, Type.FnOf fnType) {
            applyValue(locals.get(call.fn().binding()), call.args(), fnType);
        }

        /** The same, for an injected behavior a lambda captured into a slot of its own class. */
        private void applyCaptured(Core.Call call, Type.FnOf fnType) {
            applyValue(captured.get(call.fn()), call.args(), fnType);
        }

        private void applyValue(Var fv, List<Core> args, Type.FnOf fnType) {
            load(code, fv.slot(), fv.type());   // the Fn receiver
            pushInt(code, args.size());
            code.anewarray(CD_Object);
            for (int i = 0; i < args.size(); i++) {
                code.dup();
                pushInt(code, i);
                Type at = genExpr(args.get(i));
                box(code, at);
                code.aastore();
            }
            code.invokeinterface(CD_Fn, "apply", MTD_Fn_apply);
            stackCast(fnType.result());   // Object result -> the function's result type
        }

        /**
         * What a lambda's body reaches outside itself, and so what its class must be handed.
         *
         * <p>Two different things, kept apart rather than told apart afterwards: the bindings of the
         * enclosing body it reads, and the injected behaviors it calls. One is bound here and the
         * other is declared elsewhere, which is why one is held by binding and the other by name.
         */
        private static final class Reaches {

            private final LinkedHashMap<BindingId, Core.Read> reads = new LinkedHashMap<>();
            private final LinkedHashSet<String> behaviors = new LinkedHashSet<>();

            List<Core.Read> bindings() {
                return new ArrayList<>(reads.values());
            }

            List<String> injected() {
                return new ArrayList<>(behaviors);
            }
        }

        /** What {@code block}'s body reaches outside itself, in first-seen order. */
        private Reaches freeVars(Core.Block block) {
            Reaches free = new Reaches();
            Set<BindingId> bound = new HashSet<>();
            block.params().forEach(p -> bound.add(p.id()));
            collectFree(block.body(), bound, free);
            return free;
        }

        private void collectFree(Core e, Set<BindingId> bound, Reaches free) {
            switch (e) {
                case Core.Read v -> reaches(v, bound, free);
                case Core.Call c -> {
                    // an injected behavior the body calls is handed over too: the lambda is a class
                    // of its own, and what it reaches has to reach it
                    if (reqNames.contains(c.fn())) {
                        free.behaviors.add(c.fn());
                    }
                    c.args().forEach(a -> collectFree(a, bound, free));
                }
                case Core.Apply a -> {
                    reaches(a.fn(), bound, free);
                    a.args().forEach(x -> collectFree(x, bound, free));
                }
                case Core.FieldAccess fa -> collectFree(fa.target(), bound, free);
                case Core.Binary bin -> {
                    collectFree(bin.left(), bound, free);
                    collectFree(bin.right(), bound, free);
                }
                case Core.Neg neg -> collectFree(neg.operand(), bound, free);
                case Core.NewData nd -> {
                    nd.inits().forEach(i -> collectFree(i.value(), bound, free));
                    nd.spreads().forEach(sp -> reaches(sp, bound, free));
                }
                case Core.If iff -> {
                    collectFree(iff.cond(), bound, free);
                    collectFree(iff.then(), bound, free);
                    collectFree(iff.els(), bound, free);
                }
                case Core.IfConstructed ic -> {
                    collectFree(ic.construct(), bound, free);
                    collectFree(ic.then(), with(bound, ic.binder().id()), free);
                    ic.els().forEach(arm -> collectFree(arm.body(), bound, free));
                }
                case Core.LetIn li -> {
                    collectFree(li.value(), bound, free);
                    collectFree(li.body(), with(bound, li.binder().id()), free);
                }
                case Core.Match m -> {
                    collectFree(m.scrutinee(), bound, free);
                    for (Core.Case c : m.cases()) {
                        collectFree(c.body(), c.binding() == null
                                ? bound : with(bound, c.binding().id()), free);
                    }
                }
                case Core.Block b -> {
                    Set<BindingId> inner = new HashSet<>(bound);
                    b.params().forEach(p -> inner.add(p.id()));
                    collectFree(b.body(), inner, free);
                }
                case Core.ListLit lit -> lit.elements().forEach(x -> collectFree(x, bound, free));
                case Core.OptionSome so -> collectFree(so.value(), bound, free);
                case Core.Tuple t -> t.elements().forEach(x -> collectFree(x, bound, free));
                case Core.TupleGet tg -> collectFree(tg.tuple(), bound, free);
                case Core.OptionNone _ -> { }
                case Core.Int _ -> { }
                case Core.Decimal _ -> { }
                case Core.Str _ -> { }
                case Core.Bool _ -> { }
                case Core.Unreachable _ -> { }
                // neither reads anything the enclosing body binds
                case Core.UnitValue _ -> { }
                case Core.Builtin _ -> { }
            }
        }

        private static Set<BindingId> with(Set<BindingId> bound, BindingId binding) {
            Set<BindingId> inner = new HashSet<>(bound);
            inner.add(binding);
            return inner;
        }

        /** A read of something bound outside the lambda is captured; one of its own is not. */
        private void reaches(Core.Read read, Set<BindingId> bound, Reaches free) {
            if (!bound.contains(read.binding()) && locals.containsKey(read.binding())) {
                free.reads.putIfAbsent(read.binding(), read);
            }
        }

    /** Where a value lives and what it is. {@code name} is what it is called — a diagnostic quotes
     * it, and the checker's inference helpers are handed a view keyed by it; nothing is found by it. */
    private record Var(int slot, Type type, String name) {}
}
