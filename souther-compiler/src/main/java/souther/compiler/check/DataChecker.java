package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The declaration-level checks: a {@code data}'s fields and invariant, a sum's cases, the decoder
 * and encoder written against them, and every construction of an invariant-bearing type.
 *
 * <p>These run per definition, so a failure in one is collected and the next is still checked
 * (see {@code TypeChecker.collect}).
 */
public final class DataChecker {

    private DataChecker() {}

    /** A constant newtype construction to verify after codegen: its wrapped constant and its site. */
    public record ConstCheck(String typeName, Object value, SourcePos pos) {}

    /**
     * Every {@code 金額(constant)} in the module: a newtype construction whose argument folds to a
     * compile-time constant. The compiler runs each through the generated {@code $Ctfe.check}
     * (CTFE) so a violation becomes a compile error rather than a run-time abort (ADR-0032).
     */
    public static List<ConstCheck> constNewtypeChecks(Ast.Module module, Map<String, Ast.Def> symbols) {
        List<ConstCheck> out = new ArrayList<>();
        for (Ast.FnDef fn : module.fns()) {
            collectConstChecks(fn.body(), symbols, out);
        }
        return out;
    }

    private static void collectConstChecks(Ast.Expr e, Map<String, Ast.Def> symbols, List<ConstCheck> out) {
        if (e instanceof Ast.NewData nd && symbols.get(nd.typeName()) instanceof Ast.Data nt
                && nt.newtype() && isInvariantBearing(nd.typeName(), symbols)) {
            CallElaborator.newtypeConstantArg(nd).ifPresent(v -> out.add(new ConstCheck(nd.typeName(), v, nd.pos())));
        }
        TypeChecker.forEachChild(e, c -> collectConstChecks(c, symbols, out));
    }

    public static boolean isInvariantBearing(String typeName, Map<String, Ast.Def> symbols) {
        return symbols.get(typeName) instanceof Ast.Data d && !TypeOps.effectiveInvariants(d, symbols).isEmpty();
    }

    /**
     * The data types {@code e} constructs.
     *
     * <p>{@code bound} carries the names in scope, because a bare identifier is a unit data's
     * construction only when nothing has bound it — a local of the same name wins (spec 8.4).
     * Without it, a parameter named after a unit data was read as constructing that unit.
     */
    static void collectConstructs(Ast.Expr e, Set<String> out, Map<String, Ast.Def> symbols,
                                          Set<String> bound, Map<String, Set<String>> recConstructs) {
        switch (e) {
            case Ast.LetIn li -> {
                collectConstructs(li.value(), out, symbols, bound, recConstructs);
                Set<String> inner = new HashSet<>(bound);
                inner.add(li.name());
                collectConstructs(li.body(), out, symbols, inner, recConstructs);
            }
            case Ast.NewData nd -> {
                out.add(nd.typeName());
                for (Ast.FieldInit init : nd.inits()) {
                    collectConstructs(init.value(), out, symbols, bound, recConstructs);
                }
            }
            case Ast.FieldAccess fa -> collectConstructs(fa.target(), out, symbols, bound, recConstructs);
            case Ast.Tuple tup -> tup.elements().forEach(el -> collectConstructs(el, out, symbols, bound, recConstructs));
            case Ast.TupleGet tg -> collectConstructs(tg.tuple(), out, symbols, bound, recConstructs);
            case Ast.Call call -> {
                // a recursive helper is not inlined, so its own (transitive) constructions are
                // attributed to the behavior that calls it, exactly as an inlined helper's would be.
                Set<String> viaHelper = recConstructs.get(call.fn());
                if (viaHelper != null) {
                    out.addAll(viaHelper);
                }
                call.args().forEach(a -> collectConstructs(a, out, symbols, bound, recConstructs));
            }
            case Ast.Binary bin -> {
                collectConstructs(bin.left(), out, symbols, bound, recConstructs);
                collectConstructs(bin.right(), out, symbols, bound, recConstructs);
            }
            case Ast.Neg neg -> collectConstructs(neg.operand(), out, symbols, bound, recConstructs);
            case Ast.Match m -> {
                collectConstructs(m.scrutinee(), out, symbols, bound, recConstructs);
                for (Ast.Case c : m.cases()) {
                    Set<String> inner = new HashSet<>(bound);
                    if (c.binding() != null) {
                        inner.add(c.binding());
                    }
                    collectConstructs(c.body(), out, symbols, inner, recConstructs);
                }
            }
            case Ast.If iff -> {
                collectConstructs(iff.cond(), out, symbols, bound, recConstructs);
                collectConstructs(iff.then(), out, symbols, bound, recConstructs);
                collectConstructs(iff.els(), out, symbols, bound, recConstructs);
            }
            case Ast.ListLit lit -> lit.elements().forEach(el -> collectConstructs(el, out, symbols, bound, recConstructs));
            case Ast.ListComp comp -> {
                collectConstructs(comp.element(), out, symbols, bound, recConstructs);
                comp.guards().forEach(g -> collectConstructs(g, out, symbols, bound, recConstructs));
            }
            case Ast.Block block -> {
                // a block builds under the enclosing behavior's permission (spec 12.5)
                Set<String> inner = new HashSet<>(bound);
                inner.addAll(block.params());
                collectConstructs(block.body(), out, symbols, inner, recConstructs);
            }
            // a bare name that resolves to a unit data is that unit's construction (spec 8.4)
            case Ast.Var v when !bound.contains(v.name())
                    && symbols.get(v.name()) instanceof Ast.UnitData -> out.add(v.name());
            case Ast.IntLit _ -> { }
            case Ast.DecimalLit _ -> { }
            case Ast.StringLit _ -> { }
            case Ast.BoolLit _ -> { }
            case Ast.Var _ -> { }
        }
    }

    /** Rejects a name listed more than once in a declaration ({@code where}). The duplicate is
     * meaningless and, left to codegen, would emit a duplicate JVM member — a duplicate method,
     * field, or implemented interface, i.e. a malformed class file. */
    static void rejectDuplicateNames(List<String> names, String where, SourcePos pos) {
        Set<String> seen = new HashSet<>();
        for (String n : names) {
            if (!seen.add(n)) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.dup.name").title("check.duplicate.title")
                                .at(pos).args(n, where).build(),
                        "`" + n + "` is listed more than once in " + where);
            }
        }
    }

    static void checkSum(Ast.SumData sum, Map<String, Ast.Def> symbols) {
        rejectDuplicateNames(sum.cases(), "the sum `" + sum.name() + "`", sum.pos());
        for (String caseName : sum.cases()) {
            if (!symbols.containsKey(caseName)) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.sum.unknowncase").title("check.sum.title")
                                .at(sum.pos()).args(caseName, sum.name()).build(),
                        "unknown case `" + caseName + "` in sum `" + sum.name() + "`");
            }
        }
        sum.decoder().ifPresent(disc -> {
            // a derived codec dispatches over the leaves, so a nested sum's cases count too (8.3, 10.3)
            Set<String> dispatchable = TypeOps.leafCases(Type.ref(sum.name()), symbols);
            for (Ast.Variant v : disc.variants()) {
                Ast.Def caseDef = symbols.get(v.caseType());
                if (caseDef == null || !dispatchable.contains(v.caseType())) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.codec.notcase").title("check.codec.title")
                                    .at(v.pos()).args(v.caseType(), sum.name()).build(),
                            "variant `" + v.caseType() + "` is not a case of `" + sum.name() + "`");
                }
                // a unit-data case has an implicit (field-less) decoder generated on its class;
                // a case may itself be a sum (spec 8.3's nested `自社負担 | 先方負担`)
                boolean caseDecodes = caseDef instanceof Ast.UnitData
                        || (caseDef instanceof Ast.Data d && d.decoder().isPresent())
                        || (caseDef instanceof Ast.SumData s && s.decoder().isPresent());
                if (!caseDecodes) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.codec.needdecoder").title("check.codec.title")
                                    .at(v.pos()).args(v.caseType()).build(),
                            "variant `" + v.caseType() + "` needs a decoder");
                }
            }
        });
        sum.encoder().ifPresent(enc -> {
            Set<String> covered = new HashSet<>();
            Set<String> encodable = TypeOps.leafCases(Type.ref(sum.name()), symbols);
            for (Ast.EncVariant v : enc.variants()) {
                if (!encodable.contains(v.caseType())) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.codec.notcase").title("check.codec.title")
                                    .at(v.pos()).args(v.caseType(), sum.name()).build(),
                            "`" + v.caseType() + "` is not a case of `" + sum.name() + "`");
                }
                Ast.Def caseDef = symbols.get(v.caseType());
                boolean caseEncodes = caseDef instanceof Ast.UnitData
                        || (caseDef instanceof Ast.Data d && d.encoder().isPresent())
                        || (caseDef instanceof Ast.SumData s && s.encoder().isPresent());
                if (!caseEncodes) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.codec.needencoder").title("check.codec.title")
                                    .at(v.pos()).args(v.caseType()).build(),
                            "case `" + v.caseType() + "` needs an encoder");
                }
                covered.add(v.caseType());
            }
            for (String caseName : encodable) {
                if (!covered.contains(caseName)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.codec.missingcase").title("check.codec.title")
                                    .at(enc.pos()).args(sum.name(), caseName).build(),
                            "encoder for `" + sum.name() + "` is missing case `" + caseName + "`");
                }
            }
        });
    }

    /**
     * Rejects a data whose construction requires constructing itself through mandatory fields with no
     * base case — a base-less cycle is uninhabitable, so no value can ever be built. An optional
     * ({@code ?}) field or a {@code List}/{@code Map} field is a base case ({@code None} or the empty
     * collection breaks the cycle), so it does not count as a mandatory edge. A sum is OR-composed —
     * a cycle routed through one may bottom out in another case — so the walk stops at a sum rather
     * than raise a false positive.
     */
    static void checkNoUninhabitableCycle(Ast.Module module, Map<String, Ast.Def> symbols) {
        for (Ast.Def def : module.defs()) {
            if (def instanceof Ast.Data data
                    && mandatoryReaches(data.name(), data.name(), symbols, new HashSet<>())) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.construct.self").title("check.construct.title")
                                .at(data.pos()).args(data.name()).build(),
                        "data `" + data.name() + "` cannot be constructed:"
                                + " it needs a value of itself through a mandatory field, with no `?` or"
                                + " `List` to bottom out — make the self-referring field optional (`?`)"
                                + " or a `List`.");
            }
        }
    }

    /** Whether {@code target} is reachable from {@code from} through mandatory data-typed fields. A
     * plain field of a record/newtype type is a {@link Type.Ref}; an optional, list, or map field is
     * not, so only mandatory references form edges. */
    private static boolean mandatoryReaches(String from, String target, Map<String, Ast.Def> symbols,
                                            Set<String> seen) {
        if (!(symbols.get(from) instanceof Ast.Data d)) {
            return false;   // a sum (OR-composed) or unit (field-less) breaks the mandatory chain
        }
        for (Type ft : TypeOps.fieldTypes(d, symbols).values()) {
            if (ft instanceof Type.Ref ref) {
                if (ref.name().equals(target)) {
                    return true;
                }
                if (seen.add(ref.name()) && mandatoryReaches(ref.name(), target, symbols, seen)) {
                    return true;
                }
            }
        }
        return false;
    }

    static void checkData(CheckContext ctx,
                                  Map<String, Type> recursiveHelperFns) {
        Map<String, Type> fields = TypeOps.fieldTypes(ctx.data(), ctx.symbols());

        for (Map.Entry<String, Type> e : fields.entrySet()) {
            if (SpecChecker.containsTuple(e.getValue())) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.field.tuple").title("check.boundary.title")
                                .at(ctx.data().pos()).args(ctx.data().name(), e.getKey()).build(),
                        "a tuple cannot be a data field (`" + ctx.data().name() + "." + e.getKey()
                                + "`): a tuple has no external representation, so it cannot cross a"
                                + " decoder/encoder boundary (ADR-0036). Use a named data.");
            }
        }

        ctx.data().invariant().ifPresent(expr -> {
            // A total recursive helper — the stdlib fold behind the list quantifiers, or a user helper
            // proven total — is callable from an invariant, so its signature must be in scope here. A
            // field of the same name as a helper wins: a bare name in an invariant is a field reference.
            Map<String, Type> invEnv = new HashMap<>(recursiveHelperFns);
            invEnv.putAll(fields);
            Type t = Elaborator.typeOf(expr, invEnv, ctx);
            if (t != Type.BOOL) {
                throw CompileException.of(
                        Diagnostic.of("E1101", "e1101.msg").at(expr.pos()).args(Type.show(t)).build(),
                        "Invariant expression must have type Bool. Found: " + t);
            }
        });

        ctx.data().decoder().ifPresent(dec -> checkDecoder(dec, ctx, fields));
        ctx.data().encoder().ifPresent(enc -> checkEncoder(enc, ctx));
    }

    private static void checkDecoder(Ast.DecoderDef dec, CheckContext ctx, Map<String, Type> fields) {
        switch (dec) {
            case Ast.PrimDecoder prim -> {
                Type inputType = TypeOps.primType(prim.from());
                Map<String, Type> env = new HashMap<>();
                env.put(prim.inputName(), inputType);
                for (Ast.DecStmt stmt : prim.stmts()) {
                    switch (stmt) {
                        case Ast.Let let -> env.put(let.name(), Elaborator.typeOf(let.value(), env, ctx));
                    }
                }
                checkConstruct(prim.result(), ctx, fields, env);
            }
            case Ast.ObjectDecoder obj -> {
                Map<String, Type> env = new HashMap<>();
                for (Ast.Bind bind : obj.binds()) {
                    env.put(bind.name(), decRefType(bind.ref(), ctx.symbols()));
                }
                checkConstruct(obj.result(), ctx, fields, env);
            }
            case Ast.NewtypeDecoder nt -> {
                Map<String, Type> env = new HashMap<>();
                env.put(nt.inputName(), decRefType(nt.inner(), ctx.symbols()));
                checkConstruct(nt.result(), ctx, fields, env);
            }
        }
    }

    private static Type decRefType(Ast.DecRef ref, Map<String, Ast.Def> symbols) {
        return switch (ref) {
            case Ast.SetDecRef s -> Type.set(decRefType(s.element(), symbols));
            case Ast.PrimDecRef p -> TypeOps.primType(p.kind());
            case Ast.DataDecRef d -> {
                Ast.Def def = symbols.get(d.typeName());
                boolean hasDecoder = (def instanceof Ast.Data dd && dd.decoder().isPresent())
                        || (def instanceof Ast.SumData s && s.decoder().isPresent());
                if (!hasDecoder) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.codec.nodecoder").title("check.codec.title")
                                    .at(d.pos()).args(d.typeName()).build(),
                            "`" + d.typeName() + "` has no decoder to call `" + d.typeName() + ".decoder`");
                }
                yield Type.ref(d.typeName());
            }
            case Ast.ListDecRef l -> Type.list(decRefType(l.element(), symbols));
            case Ast.OptionDecRef o -> Type.option(decRefType(o.element(), symbols));
            case Ast.MapDecRef mp -> Type.map(
                    mp.keyType() == null ? Type.STRING : Type.ref(mp.keyType()),
                    decRefType(mp.value(), symbols));
        };
    }

    private static void checkConstruct(Ast.Construct c, CheckContext ctx, Map<String, Type> fields,
                                       Map<String, Type> env) {
        if (!c.typeName().equals(ctx.data().name())) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.codec.mustconstruct").title("check.codec.title")
                            .at(c.pos()).args(ctx.data().name(), c.typeName()).build(),
                    "decoder for `" + ctx.data().name() + "` must construct `" + ctx.data().name()
                            + "`, but constructs `" + c.typeName() + "`");
        }
        checkConstruction(c.typeName(), c.inits(), c.spreads(), c.pos(), fields, env, ctx);
    }

    static List<Core.FieldInit> checkConstruction(String typeName, List<Ast.FieldInit> inits,
                                          List<String> spreads,
                                          SourcePos pos, Map<String, Type> fields, Map<String, Type> env,
                                          CheckContext ctx) {
        Map<String, Ast.FieldInit> byName = new HashMap<>();
        List<Core.FieldInit> elaborated = new ArrayList<>();
        for (Ast.FieldInit init : inits) {
            if (byName.put(init.name(), init) != null) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.dup.field").title("check.duplicate.title")
                                .at(init.pos()).args(init.name()).build(),
                        "duplicate field `" + init.name() + "`");
            }
            Type ft = fields.get(init.name());
            if (ft == null) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.construct.nofield").title("check.construct.title")
                                .at(init.pos(), init.name().length()).args(init.name(), typeName).build(),
                        "`" + init.name() + "` is not a field of `" + typeName + "`");
            }
            // push the field's declared type into the value expression, so a field initialised from a
            // fold over an empty-collection seed has its result pinned by the field type (issue #70)
            Core value = Elaborator.elaborate(init.value(), env, ctx, ft);
            elaborated.add(new Core.FieldInit(init.name(), value, init.pos()));
            Type vt = value.type();
            if (!TypeOps.assignable(vt, ft, ctx.symbols())) {   // a case value widens to its sum-typed field (spec 8.3)
                throw CompileException.of(
                        Diagnostic.of(null, "check.field.type").title("check.type.mismatch.title")
                                .at(init.pos(), init.name().length())
                                .args(init.name(), Type.show(ft), Type.show(vt))
                                .diff(Type.show(vt), Type.show(ft)).build(),
                        "field `" + init.name() + "` expects " + ft + " but got " + vt);
            }
        }
        Map<String, Type> provided = new HashMap<>();
        for (String sp : spreads) {
            if (!(env.get(sp) instanceof Type.Ref ref)
                    || !(ctx.symbols().get(ref.name()) instanceof Ast.Data sd)) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.spread.notdata").title("check.construct.title")
                                .at(pos).args(sp).build(),
                        "spread `.." + sp + "` must be a data value");
            }
            provided.putAll(TypeOps.fieldTypes(sd, ctx.symbols()));
        }
        for (Map.Entry<String, Type> f : fields.entrySet()) {
            if (byName.containsKey(f.getKey())) {
                continue;
            }
            Type pv = provided.get(f.getKey());
            if (pv == null) {
                throw CompileException.of(
                        Diagnostic.of("E1005", "e1005.msg").at(pos)
                                .args(typeName, f.getKey()).hint("e1005.hint").build(),
                        "construction of `" + typeName + "` is missing field `" + f.getKey() + "`");
            }
            if (!TypeOps.assignable(pv, f.getValue(), ctx.symbols())) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.spread.provides").title("check.type.mismatch.title")
                                .at(pos).args(f.getKey(), Type.show(pv), typeName, Type.show(f.getValue()))
                                .diff(Type.show(pv), Type.show(f.getValue())).build(),
                        "spread provides `" + f.getKey() + "` as " + pv + " but `" + typeName + "` needs "
                                + f.getValue());
            }
        }
        return elaborated;
    }

    private static void checkEncoder(Ast.EncoderDef enc, CheckContext ctx) {
        Map<String, Type> env = Map.of(enc.selfName(), Type.ref(ctx.data().name()));
        checkRawExpr(enc.result(), env, ctx);
    }

    private static void checkRawExpr(Ast.RawExpr raw, Map<String, Type> env, CheckContext ctx) {
        switch (raw) {
            case Ast.TextRaw t -> Elaborator.requireType(t.arg(), Type.STRING, env, ctx,
                    "argument of Text");
            case Ast.IntRaw i -> Elaborator.requireType(i.arg(), Type.INT, env, ctx,
                    "argument of Int");
            case Ast.BoolRaw b -> Elaborator.requireType(b.arg(), Type.BOOL, env, ctx,
                    "argument of Bool");
            case Ast.DecimalRaw d -> Elaborator.requireType(d.arg(), Type.DECIMAL, env, ctx,
                    "argument of Decimal");
            case Ast.IsoTextRaw t -> {
                Type at = Elaborator.typeOf(t.arg(), env, ctx);
                if (at != Type.DATE && at != Type.DATETIME) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.codec.iso").title("check.codec.title")
                                    .at(t.pos()).args(Type.show(at)).build(),
                            "ISO text encoder expects Date or DateTime, got " + at);
                }
            }
            case Ast.OptionRaw o -> {
                Type at = Elaborator.typeOf(o.access(), env, ctx);
                if (!(at instanceof Type.OptionOf oo)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.codec.option").title("check.codec.title")
                                    .at(o.pos()).args(Type.show(at)).build(),
                            "optional encoder expects an Option, got " + at);
                }
                Map<String, Type> inner = new HashMap<>(env);
                inner.put(o.elemVar(), oo.element());
                checkRawExpr(o.inner(), inner, ctx);
            }
            case Ast.ObjectRaw o -> {
                for (Ast.RawEntry entry : o.entries()) {
                    checkRawExpr(entry.value(), env, ctx);
                }
            }
            case Ast.EncodeRaw e -> {
                Ast.Def encDef = ctx.symbols().get(e.typeName());
                boolean hasEncoder = (encDef instanceof Ast.Data ed && ed.encoder().isPresent())
                        || (encDef instanceof Ast.SumData sd && sd.encoder().isPresent());
                if (!hasEncoder) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.codec.noencoder").title("check.codec.title")
                                    .at(e.pos()).args(e.typeName()).build(),
                            "`" + e.typeName() + "` has no encoder to call `" + e.typeName() + ".encode`");
                }
                Elaborator.requireType(e.arg(), Type.ref(e.typeName()), env, ctx,
                        "argument of " + e.typeName() + ".encode");
            }
            case Ast.ListEnc le -> {
                Type st = Elaborator.typeOf(le.source(), env, ctx);
                if (!(st instanceof Type.ListOf lo)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.codec.listsource").title("check.codec.title")
                                    .at(le.pos()).args(Type.show(st)).build(),
                            "list(...) source must be a List, got " + st);
                }
                checkEncElem(le.elem(), lo.element(), le.pos(), ctx.symbols());
            }
            case Ast.SetEnc se -> {
                Type st = Elaborator.typeOf(se.source(), env, ctx);
                if (!(st instanceof Type.SetOf so)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.codec.setsource").title("check.codec.title")
                                    .at(se.pos()).args(Type.show(st)).build(),
                            "set encoder source must be a Set, got " + st);
                }
                checkEncElem(se.elem(), so.element(), se.pos(), ctx.symbols());
            }
            case Ast.MapEnc me -> {
                Type st = Elaborator.typeOf(me.source(), env, ctx);
                if (!(st instanceof Type.MapOf mo)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.codec.mapsource").title("check.codec.title")
                                    .at(me.pos()).args(Type.show(st)).build(),
                            "map encoder source must be a Map, got " + st);
                }
                checkEncElem(me.elem(), mo.value(), me.pos(), ctx.symbols());
            }
        }
    }

    private static void checkEncElem(Ast.EncElem elem, Type elemType, SourcePos pos,
                                     Map<String, Ast.Def> symbols) {
        switch (elem) {
            case Ast.PrimEnc p -> {
                if (!elemType.equals(TypeOps.primType(p.kind()))) {
                    throw elemEncMismatch(Type.show(TypeOps.primType(p.kind())), elemType, pos);
                }
            }
            case Ast.DataEnc d -> {
                // the element may be a product or a sum: `List<事前承認理由>` holds a sum (spec 11.2)
                Ast.Def def = symbols.get(d.typeName());
                boolean hasEncoder = (def instanceof Ast.Data dd && dd.encoder().isPresent())
                        || (def instanceof Ast.SumData sd && sd.encoder().isPresent());
                if (!elemType.equals(Type.ref(d.typeName())) || !hasEncoder) {
                    throw elemEncMismatch(d.typeName(), elemType, pos);
                }
            }
            // a collection element is itself a collection: descend both the encoder and the type
            case Ast.ListElemEnc l -> {
                if (!(elemType instanceof Type.ListOf lo)) {
                    throw elemEncMismatch("List", elemType, pos);
                }
                checkEncElem(l.elem(), lo.element(), pos, symbols);
            }
            case Ast.SetElemEnc s -> {
                if (!(elemType instanceof Type.SetOf so)) {
                    throw elemEncMismatch("Set", elemType, pos);
                }
                checkEncElem(s.elem(), so.element(), pos, symbols);
            }
            case Ast.MapElemEnc m -> {
                if (!(elemType instanceof Type.MapOf mo)) {
                    throw elemEncMismatch("Map", elemType, pos);
                }
                checkEncElem(m.value(), mo.value(), pos, symbols);
            }
        }
    }

    /** The element encoder and the element type disagree, both named as they are written — the
     * encoder by the type it encodes (`String`, `商品ID`, `List`), the element by {@link Type#show}. */
    private static CompileException elemEncMismatch(String encoder, Type elemType, SourcePos pos) {
        return CompileException.of(
                Diagnostic.of(null, "check.codec.elemenc").title("check.codec.title")
                        .at(pos).args("`" + encoder + "`", Type.show(elemType)).build(),
                "element encoder `" + encoder + "` does not match " + Type.show(elemType));
    }

}
