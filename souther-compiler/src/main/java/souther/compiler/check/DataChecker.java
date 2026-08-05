package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.types.ValueName;

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

    /** The no-argument methods of {@code Object}: a field of one of these names would generate an
     * accessor that collides with a method the class already has, so none can be a field name. This is
     * the same list the JLS keeps a record component off. */
    private static final Set<String> OBJECT_METHOD_NAMES = Set.of(
            "clone", "finalize", "getClass", "hashCode", "notify", "notifyAll", "toString", "wait");

    /** A constant newtype construction to verify after codegen: its wrapped constant and its site.
     * {@code type} says which module declared it — the check runs that module's generated class, not
     * one named after the module the construction is written in. {@code typeName} is what was
     * written, which is what the message quotes. */
    public record ConstCheck(String typeName, TypeName type, Object value, SourcePos pos) {}

    /**
     * Every {@code 金額(constant)} in the module: a newtype construction whose argument folds to a
     * compile-time constant. The compiler runs each through the generated {@code $Ctfe.check}
     * (CTFE) so a violation becomes a compile error rather than a run-time abort (ADR-0032).
     */
    public static List<ConstCheck> constNewtypeChecks(Ast.Module module, Symbols symbols) {
        List<ConstCheck> out = new ArrayList<>();
        for (Ast.FnDef fn : module.fns()) {
            collectConstChecks(fn.written(), symbols, out);
        }
        return out;
    }

    private static void collectConstChecks(Ast.Expr e, Symbols symbols, List<ConstCheck> out) {
        if (e instanceof Ast.NewData nd && symbols.get(nd.typeName().denotes()) instanceof Ast.Data nt
                && nt.newtype() && isInvariantBearing(nd.typeName().denotes(), symbols)) {
            CallElaborator.newtypeConstantArg(nd).ifPresent(v ->
                    out.add(new ConstCheck(nd.typeName().written(), nd.typeName().denotes(), v, nd.pos())));
        }
        TypeChecker.forEachChild(e, c -> collectConstChecks(c, symbols, out));
    }

    public static boolean isInvariantBearing(TypeName typeName, Symbols symbols) {
        return typeName != null && symbols.get(typeName) instanceof Ast.Data d
                && !TypeOps.effectiveInvariants(d, symbols).isEmpty();
    }

    /**
     * No two clauses that apply to a data share a name. A spread carries the clauses of what it takes
     * in, names included, so the clash this reports is between a clause written here and one arriving
     * by spread as often as between two written here — and either way an arm naming it would answer
     * neither rule in particular.
     */
    private static void checkClauseNames(Ast.Data data, Symbols symbols) {
        Set<String> seen = new HashSet<>();
        for (Ast.InvariantClause clause : TypeOps.effectiveInvariants(data, symbols)) {
            String name = clause.name().orElse(null);
            if (name != null && !seen.add(name)) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.invariant.duplicate")
                                .title("check.invariant.invalid.title")
                                .at(clause.pos()).args(name, data.name()).build(),
                        "two invariant clauses of `" + data.name() + "` are named `" + name + "`");
            }
        }
    }

    /**
     * What a body builds, in the two kinds a permission check tells apart: {@code originated} is what
     * this body is answerable for, {@code carried} what another module's published value or helper
     * built and this body was handed. Each maps the type to the spelling it was written with, so a
     * report quotes the source.
     *
     * <p>The split is what makes the carried ones invisible to the requirement and still visible to
     * the redundancy check: a behavior does not have to declare `constructs` for a construction that
     * came in with a published body — it may have no name for the type — and a behavior that declares
     * one anyway is not told it builds nothing.
     */
    public record Constructs(Map<TypeName, String> originated, Map<TypeName, String> carried) {

        public static Constructs empty() {
            return new Constructs(new LinkedHashMap<>(), new LinkedHashMap<>());
        }

        /** Whether {@code built} is built here at all, however it got here. */
        public boolean builds(TypeName built) {
            return originated.containsKey(built) || carried.containsKey(built);
        }

        public Constructs copy() {
            return new Constructs(new LinkedHashMap<>(originated), new LinkedHashMap<>(carried));
        }

        /** The same set with everything counted as carried — what a body reached through something
         * it was handed rather than wrote, and so answers for none of. */
        public Constructs allCarried() {
            Map<TypeName, String> all = new LinkedHashMap<>(carried);
            originated.forEach(all::putIfAbsent);
            return new Constructs(new LinkedHashMap<>(), all);
        }

        /** Takes on everything {@code other} builds, each kind staying the kind it is, and answers
         * whether that added anything. */
        public boolean absorb(Constructs other) {
            boolean added = false;
            for (Map.Entry<TypeName, String> e : other.originated.entrySet()) {
                added |= originated.putIfAbsent(e.getKey(), e.getValue()) == null;
            }
            for (Map.Entry<TypeName, String> e : other.carried.entrySet()) {
                added |= carried.putIfAbsent(e.getKey(), e.getValue()) == null;
            }
            return added;
        }
    }

    /**
     * The data types {@code e} constructs.
     *
     * <p>{@code bound} carries the names in scope, because a bare identifier is a unit data's
     * construction only when nothing has bound it — a local of the same name wins (spec 8.4).
     * Without it, a parameter named after a unit data was read as constructing that unit.
     */
    static void collectConstructs(Ast.Expr e, Map<TypeName, String> out, Symbols symbols,
                                  Map<String, Constructs> recConstructs) {
        Constructs all = Constructs.empty();
        collectConstructs(e, all, symbols, recConstructs);
        out.putAll(all.originated());
    }

    /** Whether {@code nd} arrived here already made, rather than being written here. */
    private static boolean carried(Ast.NewData nd, TypeName built) {
        return nd.origin().carried(built);
    }

    static void collectConstructs(Ast.Expr e, Constructs out, Symbols symbols,
                                          Map<String, Constructs> recConstructs) {
        switch (e) {
            case Ast.LetIn li -> {
                collectConstructs(li.value(), out, symbols, recConstructs);
                collectConstructs(li.body(), out, symbols, recConstructs);
            }
            // An expansion builds what its arguments build and what the callee's body builds. What a
            // function argument builds is counted from the body, where the callee applies it; counted
            // here as well, one lambda's construction would be recorded twice.
            case Ast.Expansion ex -> {
                for (Ast.Bound b : ex.bound()) {
                    collectConstructs(b.value(), out, symbols, recConstructs);
                }
                collectConstructs(ex.body(), out, symbols, recConstructs);
            }
            case Ast.NewData nd -> {
                // A construction this body was handed is not this body's. It is handed one two ways.
                // A module's published value or helper carries its own: publishing the definition is
                // what states that origination, and the reader has no name to declare a type the
                // module keeps to itself by. What that does not cover is a type of some *other*
                // module the published body happened to build — that origination is neither the
                // reader's nor the publisher's to state, so it stays this behavior's to declare,
                // which it can. A value carries the construction its definition made, whatever module
                // declares the type: the definition is where the value is made, and a body that names
                // it compares against a limit rather than setting one.
                Map<TypeName, String> side = carried(nd, nd.typeName().denotes())
                        ? out.carried() : out.originated();
                side.putIfAbsent(nd.typeName().denotes(), nd.typeName().written());
                for (Ast.FieldInit init : nd.inits()) {
                    collectConstructs(init.value(), out, symbols, recConstructs);
                }
            }
            case Ast.FieldAccess fa -> collectConstructs(fa.target(), out, symbols, recConstructs);
            case Ast.Tuple tup -> tup.elements().forEach(el -> collectConstructs(el, out, symbols, recConstructs));
            case Ast.TupleGet tg -> collectConstructs(tg.tuple(), out, symbols, recConstructs);
            case Ast.Apply call -> {
                // a recursive helper is not inlined, so its own (transitive) constructions are
                // attributed to the behavior that calls it, exactly as an inlined helper's would be —
                // each as the kind it already is, so one another module published stays that
                // module's here as it does when the body is expanded. Where the call itself came in
                // on a value, none of them are this body's: the value's definition is what reached
                // the helper, and the call is standing in for constructions that would have been
                // marked had the helper been expandable.
                Constructs viaHelper = recConstructs.get(call.reaches());
                if (viaHelper != null) {
                    out.absorb(call.origin().viaValueReference() ? viaHelper.allCarried() : viaHelper);
                }
                call.args().forEach(a -> collectConstructs(a, out, symbols, recConstructs));
            }
            case Ast.Binary bin -> {
                collectConstructs(bin.left(), out, symbols, recConstructs);
                collectConstructs(bin.right(), out, symbols, recConstructs);
            }
            case Ast.Neg neg -> collectConstructs(neg.operand(), out, symbols, recConstructs);
            case Ast.Match m -> {
                collectConstructs(m.scrutinee(), out, symbols, recConstructs);
                for (Ast.Case c : m.cases()) {
                    collectConstructs(c.body(), out, symbols, recConstructs);
                }
            }
            case Ast.If iff -> {
                collectConstructs(iff.cond(), out, symbols, recConstructs);
                collectConstructs(iff.then(), out, symbols, recConstructs);
                collectConstructs(iff.els(), out, symbols, recConstructs);
            }
            // an attempt builds the value on its success branch, so it needs the same permission a
            // plain construction does — what it does not do is abort when it fails
            case Ast.IfConstructed ic -> {
                collectConstructs(ic.construct(), out, symbols, recConstructs);
                collectConstructs(ic.then(), out, symbols, recConstructs);
                ic.els().forEach(arm ->
                        collectConstructs(arm.body(), out, symbols, recConstructs));
            }
            case Ast.ListLit lit -> lit.elements().forEach(el -> collectConstructs(el, out, symbols, recConstructs));
            case Ast.ListComp comp -> {
                collectConstructs(comp.element(), out, symbols, recConstructs);
                comp.guards().forEach(g -> collectConstructs(g, out, symbols, recConstructs));
            }
            // a block builds under the enclosing behavior's permission (spec 12.5)
            case Ast.Block block -> collectConstructs(block.body(), out, symbols, recConstructs);
            // a bare name that denotes a unit data is that unit's construction (spec 8.4). Read off
            // what the name denotes rather than resolved again from its spelling: a reader with a
            // unit data spelled like the one another module's published body builds was recording
            // its own type as the one built. Carried or not is asked of the name for the same reason
            // it is asked of a construction node — it is the same question about the same thing.
            // `constructs` governs what this compilation declares; a unit the language gives
            // (`HALF_UP`) is vocabulary, not business data — as `None` is.
            case Ast.Var v when v.denotes() instanceof ValueName.OfType named
                    && symbols.declaredByCompilation(named.type())
                    && symbols.get(named.type()) instanceof Ast.UnitData -> {
                Map<TypeName, String> side = named.origin().carried(named.type())
                        ? out.carried() : out.originated();
                side.putIfAbsent(named.type(), v.name());
            }
            case Ast.IntLit _ -> { }
            case Ast.DecimalLit _ -> { }
            case Ast.StringLit _ -> { }
            case Ast.BoolLit _ -> { }
            case Ast.Var _ -> { }
            // it builds nothing: no value is made where it stands
            case Ast.Unreachable _ -> { }
        }
    }

    /** Rejects a name listed more than once in a declaration ({@code where}). The duplicate is
     * meaningless and, left to codegen, would emit a duplicate JVM member — a duplicate method,
     * field, or implemented interface, i.e. a malformed class file. */
    static void rejectDuplicateNames(List<String> names, String where, SourcePos pos) {
        Set<String> seen = new HashSet<>();
        for (String n : names) {
            if (!seen.add(n)) {
                throw duplicate(n, where, pos);
            }
        }
    }

    private static CompileException duplicate(String written, String where, SourcePos pos) {
        return CompileException.of(
                Diagnostic.of(null, "check.dup.name").title("check.duplicate.title")
                        .at(pos).args(written, where).build(),
                "`" + written + "` is listed more than once in " + where);
    }

    /**
     * As above for a list of type names. Two entries are the same when they denote one type, so
     * `Amount` an import brings in and `up.Amount` are the duplicate a spelling comparison misses.
     */
    static void rejectDuplicateTypes(List<Ast.Name> names, String where, SourcePos pos) {
        Set<TypeName> seen = new HashSet<>();
        for (Ast.Name n : names) {
            if (!seen.add(n.denotes())) {
                throw duplicate(n.written(), where, pos);
            }
        }
    }

    /** Where to point at a field the data declares — the field's own name — or at the data header for
     * one that arrived through a {@code ...} spread, which is written in the data it came from. */
    private static Region fieldRegion(Ast.Data data, String field) {
        for (Ast.Field f : data.fields()) {
            if (f.name().equals(field)) {
                return Region.ofWidth(f.pos(), field.length());
            }
        }
        return Region.point(data.pos());
    }

    /** The path back to {@code target} through sum cases, or null when it does not reach itself. A
     * sum names the values it can be, so a case that is (or reaches) the sum itself describes nothing:
     * it has no leaf to dispatch a codec over and no case list a {@code match} could be exhaustive
     * against. Reported here rather than left to the walks, which would recurse until the stack ran
     * out — codec derivation runs before this check and stops at the repeat for the same reason. */
    private static List<String> sumCycle(TypeName target, Symbols symbols,
                                         LinkedHashSet<TypeName> path) {
        if (!(symbols.get(path.isEmpty() ? target : last(path)) instanceof Ast.SumData s)) {
            return null;
        }
        for (Ast.Name caseName : s.cases()) {
            if (target.equals(caseName.denotes())) {
                List<String> out = new ArrayList<>();
                for (TypeName seen : path) {
                    out.add(seen.name());
                }
                out.add(caseName.written());
                return out;
            }
            if (symbols.get(caseName.denotes()) instanceof Ast.SumData && path.add(caseName.denotes())) {
                List<String> found = sumCycle(target, symbols, path);
                if (found != null) {
                    return found;
                }
                path.remove(caseName.denotes());
            }
        }
        return null;
    }

    private static TypeName last(LinkedHashSet<TypeName> path) {
        TypeName out = null;
        for (TypeName t : path) {
            out = t;
        }
        return out;
    }

    static void checkSum(Ast.SumData sum, Symbols symbols) {
        rejectDuplicateTypes(sum.cases(), "the sum `" + sum.name() + "`", sum.pos());
        // A generated sum is a sealed interface, and its `permits` is settled when its own module is
        // generated — a case of another module cannot implement it, so it would be permitted without
        // being a member: no value satisfies the type and an exhaustive switch over it has no arms
        // (ADR-0057, the declared-sum counterpart of E1606).
        for (Ast.Name c : sum.cases()) {
            if (symbols.isForeign(c.denotes())) {
                throw CompileException.of(
                        Diagnostic.of("E1606", "check.sum.foreigncase").title("check.sum.title")
                                .at(c.pos(), c.written().length())
                                .args(c.written(), sum.name(), c.denotes().module())
                                .hint("check.sum.foreigncase.hint").build(),
                        "`" + c.written() + "` is declared in `" + c.denotes().module() + "`, so it"
                                + " cannot be a case of `" + sum.name() + "` — a sum's cases are"
                                + " declared with it; consume it at the boundary, or re-express it as"
                                + " a case of this module");
            }
        }
        List<String> cycle = sumCycle(symbols.own(sum.name()), symbols, new LinkedHashSet<>());
        if (cycle != null) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.sum.cycle").title("check.sum.title")
                            .at(sum.pos()).args(sum.name(), String.join(" | ", cycle)).build(),
                    "sum `" + sum.name() + "` contains itself through " + String.join(" | ", cycle)
                            + "; a sum's cases are the values it can be, so one of them cannot be the"
                            + " sum itself");
        }
        sum.decoder().ifPresent(disc -> {
            // a derived codec dispatches over the leaves, so a nested sum's cases count too (8.3, 10.3)
            Set<TypeName> dispatchable = TypeOps.leafCases(Type.ref(symbols.own(sum.name())), symbols);
            for (Ast.Variant v : disc.variants()) {
                Ast.Def caseDef = symbols.get(v.caseType().denotes());
                if (!dispatchable.contains(v.caseType().denotes())) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.codec.notcase").title("check.codec.title")
                                    .at(v.pos()).args(v.caseType().written(), sum.name()).build(),
                            "variant `" + v.caseType().written() + "` is not a case of `" + sum.name() + "`");
                }
                // a unit-data case has an implicit (field-less) decoder generated on its class;
                // a case may itself be a sum (spec 8.3's nested `自社負担 | 先方負担`)
                boolean caseDecodes = caseDef instanceof Ast.UnitData
                        || (caseDef instanceof Ast.Data d && d.decoder().isPresent())
                        || (caseDef instanceof Ast.SumData s && s.decoder().isPresent());
                if (!caseDecodes) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.codec.needdecoder").title("check.codec.title")
                                    .at(v.pos()).args(v.caseType().written()).build(),
                            "variant `" + v.caseType().written() + "` needs a decoder");
                }
            }
        });
        sum.encoder().ifPresent(enc -> {
            // A case lays its fields flatly beside the discriminator the sum writes, so a case
            // declaring a field of that name and the tag want one key. Refused here rather than
            // written over where it is encoded, which would lose the value with nothing said.
            TypeName carrying = TypeOps.memberCarryingField(
                    Type.ref(symbols.own(sum.name())), enc.key(), symbols);
            if (carrying != null) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.case.discriminatorfield").title("check.codec.title")
                                .at(sum.pos()).args(carrying.name(), enc.key(), sum.name())
                                .hint("check.case.discriminatorfield.hint", enc.key()).build(),
                        "`" + carrying.name() + "` is a case of `" + sum.name() + "` and declares a"
                                + " field `" + enc.key() + "`, which is the discriminator its sum"
                                + " writes beside the fields; rename the field");
            }
            Set<TypeName> covered = new HashSet<>();
            Set<TypeName> encodable = TypeOps.leafCases(Type.ref(symbols.own(sum.name())), symbols);
            for (Ast.EncVariant v : enc.variants()) {
                if (!encodable.contains(v.caseType().denotes())) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.codec.notcase").title("check.codec.title")
                                    .at(v.pos()).args(v.caseType().written(), sum.name()).build(),
                            "`" + v.caseType().written() + "` is not a case of `" + sum.name() + "`");
                }
                Ast.Def caseDef = symbols.get(v.caseType().denotes());
                boolean caseEncodes = caseDef instanceof Ast.UnitData
                        || (caseDef instanceof Ast.Data d && d.encoder().isPresent())
                        || (caseDef instanceof Ast.SumData s && s.encoder().isPresent());
                if (!caseEncodes) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.codec.needencoder").title("check.codec.title")
                                    .at(v.pos()).args(v.caseType().written()).build(),
                            "case `" + v.caseType().written() + "` needs an encoder");
                }
                covered.add(v.caseType().denotes());
            }
            for (TypeName caseName : encodable) {
                if (!covered.contains(caseName)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.codec.missingcase").title("check.codec.title")
                                    .at(enc.pos()).args(sum.name(), caseName.name()).build(),
                            "encoder for `" + sum.name() + "` is missing case `" + caseName.name() + "`");
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
    static void checkNoUninhabitableCycle(Ast.Module module, Symbols symbols) {
        for (Ast.Def def : module.defs()) {
            if (def instanceof Ast.Data data
                    && mandatoryReaches(symbols.own(data.name()), symbols.own(data.name()),
                            symbols, new HashSet<>())) {
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
    private static boolean mandatoryReaches(TypeName from, TypeName target, Symbols symbols,
                                            Set<TypeName> seen) {
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

        // A newtype wraps one value and takes its representation, so there is nothing for it to be
        // when the value is absent. Whether a value is present is a property of the place it is
        // used, written there as `f: X?`. Read on the resolved type, so a data the author happens
        // to have named `Option` is an ordinary named data here.
        if (ctx.data().newtype() && fields.get("value") instanceof Type.OptionOf o) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.newtype.optional").title("check.boundary.title")
                            .at(fieldRegion(ctx.data(), "value"))
                            .args(ctx.data().name(), Type.show(o.element()))
                            .hint("check.newtype.optional.hint", ctx.data().name()).build(),
                    "newtype `" + ctx.data().name() + "` cannot wrap an optional; write the `?` where"
                            + " the value is used, on the field");
        }

        for (Map.Entry<String, Type> e : fields.entrySet()) {
            // A field is read through an accessor of the same name, and a data is a record over its
            // fields (spec 19.2). A no-argument method of Object is therefore taken: `toString` would
            // emit a second `toString()` and the class would not load, and the rest cannot be a record
            // component either. Reported here rather than left to codegen, as a duplicate name is.
            if (OBJECT_METHOD_NAMES.contains(e.getKey())) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.field.objectname").title("check.reserved.title")
                                .at(fieldRegion(ctx.data(), e.getKey()))
                                .args(ctx.data().name(), e.getKey()).build(),
                        "`" + e.getKey() + "` cannot be a field of `" + ctx.data().name() + "`: the"
                                + " generated class reads its fields through accessors of the same name,"
                                + " and `" + e.getKey() + "()` is already a method every JVM value has");
            }
            if (TypeOps.withoutExternalForm(e.getValue(), ctx.symbols()) instanceof Type.TupleOf) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.field.tuple").title("check.boundary.title")
                                .at(fieldRegion(ctx.data(), e.getKey()))
                                .args(ctx.data().name(), e.getKey()).build(),
                        "a tuple cannot be a data field (`" + ctx.data().name() + "." + e.getKey()
                                + "`): a tuple has no external representation, so it cannot cross a"
                                + " decoder/encoder boundary (ADR-0036). Use a named data.");
            }
            // A field is written to and read from the outside, so a map it holds is a JSON object and
            // its keys are strings. Inside a body the same map may be keyed by anything (ADR-0040).
            Type badKey = TypeOps.nonBoundaryMapKey(e.getValue(), ctx.symbols());
            if (badKey != null) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.map.key.field").title("check.boundary.title")
                                .at(fieldRegion(ctx.data(), e.getKey()))
                                .args(ctx.data().name() + "." + e.getKey(), Type.show(badKey))
                                .hint("check.map.key.field.hint").build(),
                        "a Map crossing the boundary at `" + ctx.data().name() + "." + e.getKey()
                                + "` must be keyed by String, a String-backed newtype (`data X ="
                                + " String`), Date or DateTime, got " + Type.show(badKey)
                                + " (ADR-0040)");
            }
        }

        for (Ast.InvariantClause clause : ctx.data().invariants()) {
            // A total recursive helper — the stdlib fold behind the list quantifiers, or a user helper
            // proven total — is callable from an invariant, so its signature must be in scope here. A
            // field of the same name as a helper wins: a bare name in an invariant is a field reference.
            Scope invEnv = fieldScope(ctx).reaching(recursiveHelperFns);
            // A clause is the declaration's, not the body's. Reached from a construction, this is
            // where one tree stops and another starts, so what the tree being walked keeps standing
            // is left behind: what this one keeps is its own to say, and a permission inherited by
            // being reached from somewhere is not a permission a representation gave.
            Type t = Elaborator.typeOf(clause.expr(), invEnv, ctx.inAnotherRepresentation());
            if (t != Type.BOOL) {
                throw CompileException.of(
                        Diagnostic.of("E1101", "e1101.msg").at(clause.expr().pos())
                                .args(Type.show(t)).build(),
                        "Invariant expression must have type Bool. Found: " + t);
            }
        }
        checkClauseNames(ctx.data(), ctx.symbols());

        ctx.data().decoder().ifPresent(dec -> checkDecoder(dec, ctx, fields));
        ctx.data().encoder().ifPresent(enc -> checkEncoder(enc, ctx));
    }

    /** The bindings a declaration's own invariant reads: its fields, each as the binding it is. */
    private static Scope fieldScope(CheckContext ctx) {
        Map<String, Type> types = TypeOps.fieldTypes(ctx.data(), ctx.symbols());
        Map<BindingId, Scope.Binding> bindings = new LinkedHashMap<>();
        TypeOps.fieldBindings(ctx.data(), ctx.symbols()).forEach((name, binding) ->
                bindings.put(binding, new Scope.Binding(name, types.get(name))));
        return Scope.of(bindings);
    }

    private static void checkDecoder(Ast.DecoderDef dec, CheckContext ctx, Map<String, Type> fields) {
        switch (dec) {
            case Ast.PrimDecoder prim -> {
                Type inputType = TypeOps.primType(prim.from());
                Scope env = Scope.NONE.with(prim.input(), inputType);
                for (Ast.DecStmt stmt : prim.stmts()) {
                    switch (stmt) {
                        case Ast.Let let ->
                                env = env.with(let.binder(), Elaborator.typeOf(let.value(), env, ctx));
                    }
                }
                checkConstruct(prim.result(), ctx, fields, env);
            }
            case Ast.ObjectDecoder obj -> {
                Scope env = Scope.NONE;
                for (Ast.Bind bind : obj.binds()) {
                    env = env.with(bind.binder(), decRefType(bind.ref(), ctx.symbols()));
                }
                checkConstruct(obj.result(), ctx, fields, env);
            }
            case Ast.NewtypeDecoder nt -> {
                Scope env = Scope.NONE.with(nt.input(), decRefType(nt.inner(), ctx.symbols()));
                checkConstruct(nt.result(), ctx, fields, env);
            }
        }
    }

    private static Type decRefType(Ast.DecRef ref, Symbols symbols) {
        return switch (ref) {
            case Ast.SetDecRef s -> Type.set(decRefType(s.element(), symbols));
            case Ast.PrimDecRef p -> TypeOps.primType(p.kind());
            case Ast.DataDecRef d -> {
                Ast.Def def = symbols.get(d.typeName().denotes());
                boolean hasDecoder = (def instanceof Ast.Data dd && dd.decoder().isPresent())
                        || (def instanceof Ast.SumData s && s.decoder().isPresent());
                if (!hasDecoder) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.codec.nodecoder").title("check.codec.title")
                                    .at(d.pos()).args(d.typeName().written()).build(),
                            "`" + d.typeName().written() + "` has no decoder to call `"
                                    + d.typeName().written() + ".decoder`");
                }
                yield Type.ref(d.typeName().denotes());
            }
            case Ast.ListDecRef l -> Type.list(decRefType(l.element(), symbols));
            case Ast.OptionDecRef o -> Type.option(decRefType(o.element(), symbols));
            case Ast.MapDecRef mp -> Type.map(
                    decRefType(mp.key(), symbols), decRefType(mp.value(), symbols));
        };
    }

    private static void checkConstruct(Ast.Construct c, CheckContext ctx, Map<String, Type> fields,
                                       Scope env) {
        if (!c.typeName().denotes().equals(ctx.symbols().own(ctx.data().name()))) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.codec.mustconstruct").title("check.codec.title")
                            .at(c.pos()).args(ctx.data().name(), c.typeName().written()).build(),
                    "decoder for `" + ctx.data().name() + "` must construct `" + ctx.data().name()
                            + "`, but constructs `" + c.typeName().written() + "`");
        }
        // a decoder's construction gives every field a value of its own; nothing builds one with a
        // spread, so there is no binding to copy from here
        checkConstruction(c.typeName().written(), c.inits(), List.of(), c.pos(), fields, env, ctx);
    }

    static List<Core.FieldInit> checkConstruction(String typeName, List<Ast.FieldInit> inits,
                                          List<Core.Read> spreads,
                                          SourcePos pos, Map<String, Type> fields, Scope env,
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
            // fold over an empty-collection seed has its result pinned by the field type (issue #70).
            // This is also the one place an optional may be made (ADR-0011), which the context carries
            // rather than the expected type: a model may write `Option<T>` where it reads one, so an
            // expected optional no longer means a field asked for it (issue #202).
            CheckContext making = ctx.makingAnOptional(ft instanceof Type.OptionOf);
            Core value = Elaborator.liftIntoOption(
                    Elaborator.elaborate(init.value(), env, making, ft), ft, ctx.symbols());
            elaborated.add(new Core.FieldInit(init.name(), value, init.pos()));
            Type vt = value.type();
            if (!TypeOps.assignable(vt, ft, ctx.symbols())) {   // a case value widens to its sum-typed field (spec 8.3)
                throw CompileException.of(
                        Diagnostic.of(null, "check.field.type").title("check.type.mismatch.title")
                                .at(init.pos(), init.name().length())
                                .args(init.name(), Type.show(ft), Type.show(vt))
                                .diff(Type.show(vt, ft), Type.show(ft, vt)).build(),
                        "field `" + init.name() + "` expects " + ft + " but got " + vt);
            }
        }
        Map<String, Type> provided = new HashMap<>();
        // the sums spread here, which a field the construction still wants was not in the shared part
        // of — all of them, because naming one of several would pick by position and send the author
        // to open a sum whose cases never had the field
        Set<String> fromSums = new LinkedHashSet<>();
        for (Core.Read spread : spreads) {
            String sp = spread.name();
            Type bound = env.typeOf(spread.binding());
            if (bound instanceof Type.Ref ref
                    && ctx.symbols().get(ref.name()) instanceof Ast.SumData sum) {
                fromSums.add(Type.show(bound));
                provided.putAll(spreadOfSum(sp, sum, bound, pos, ctx));
            } else if (bound instanceof Type.Ref ref
                    && ctx.symbols().get(ref.name()) instanceof Ast.Data sd) {
                provided.putAll(TypeOps.fieldTypes(sd, ctx.symbols()));
            } else {
                Diagnostic.Builder d = Diagnostic.of(null, "check.spread.notdata")
                        .title("check.construct.title").at(pos).args(sp);
                if (bound instanceof Type.Union) {
                    d = d.hint("check.spread.union.hint", sp);
                }
                throw CompileException.of(d.build(),
                        "spread `.." + sp + "` must be a data value");
            }
        }
        for (Map.Entry<String, Type> f : fields.entrySet()) {
            if (byName.containsKey(f.getKey())) {
                continue;
            }
            Type pv = provided.get(f.getKey());
            if (pv == null) {
                Diagnostic.Builder d = Diagnostic.of("E1005", "e1005.msg").at(pos)
                        .args(typeName, f.getKey());
                d = switch (fromSums.size()) {
                    case 0 -> d.hint("e1005.hint");
                    case 1 -> d.hint("e1005.hint.sum", typeName, f.getKey(),
                            fromSums.iterator().next());
                    default -> d.hint("e1005.hint.sums", typeName, f.getKey(),
                            String.join(", ", fromSums));
                };
                throw CompileException.of(d.build(),
                        "construction of `" + typeName + "` is missing field `" + f.getKey() + "`");
            }
            if (!TypeOps.assignable(pv, f.getValue(), ctx.symbols())) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.spread.provides").title("check.type.mismatch.title")
                                .at(pos).args(f.getKey(), Type.show(pv), typeName, Type.show(f.getValue()))
                                .diff(Type.show(pv, f.getValue()), Type.show(f.getValue(), pv)).build(),
                        "spread provides `" + f.getKey() + "` as " + pv + " but `" + typeName + "` needs "
                                + f.getValue());
            }
        }
        return elaborated;
    }

    /** What a spread of a sum copies: the fields of the data every one of its cases spreads. This is
     * the construction side of reading such a field off the sum, and takes its shared part from the
     * same place the read does, so the two answer alike. A sum whose cases share no spread has nothing
     * to copy — cases that merely declare a field of the same name have not shared it — and that is
     * reported here rather than left to the missing-field report, which would name a field the author
     * can see in every case. */
    private static Map<String, Type> spreadOfSum(String name, Ast.SumData sum, Type bound,
                                                 SourcePos pos, CheckContext ctx) {
        Map<String, Type> shared = TypeOps.commonSpreadFields(sum, ctx.symbols());
        if (shared.isEmpty()) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.spread.sum.unshared").title("check.construct.title")
                            .at(pos).args(name, Type.show(bound)).build(),
                    "spread `.." + name + "` copies what the cases of " + Type.show(bound)
                            + " share, and they share none");
        }
        return shared;
    }

    private static void checkEncoder(Ast.EncoderDef enc, CheckContext ctx) {
        Scope env = Scope.NONE.with(enc.self(), Type.ref(ctx.symbols().own(ctx.data().name())));
        checkRawExpr(enc.result(), env, ctx);
    }

    private static void checkRawExpr(Ast.RawExpr raw, Scope env, CheckContext ctx) {
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
                checkRawExpr(o.inner(), env.with(o.elem(), oo.element()), ctx);
            }
            case Ast.ObjectRaw o -> {
                for (Ast.RawEntry entry : o.entries()) {
                    checkRawExpr(entry.value(), env, ctx);
                }
            }
            case Ast.EncodeRaw e -> {
                Ast.Def encDef = ctx.symbols().get(e.typeName().denotes());
                boolean hasEncoder = (encDef instanceof Ast.Data ed && ed.encoder().isPresent())
                        || (encDef instanceof Ast.SumData sd && sd.encoder().isPresent());
                if (!hasEncoder) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.codec.noencoder").title("check.codec.title")
                                    .at(e.pos()).args(e.typeName().written()).build(),
                            "`" + e.typeName().written() + "` has no encoder to call `"
                                    + e.typeName().written() + ".encode`");
                }
                Elaborator.requireType(e.arg(), Type.ref(e.typeName().denotes()), env, ctx,
                        "argument of " + e.typeName().written() + ".encode");
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
                                     Symbols symbols) {
        switch (elem) {
            case Ast.PrimEnc p -> {
                if (!elemType.equals(TypeOps.primType(p.kind()))) {
                    throw elemEncMismatch(Type.show(TypeOps.primType(p.kind())), elemType, pos);
                }
            }
            case Ast.DataEnc d -> {
                // the element may be a product or a sum: `List<事前承認理由>` holds a sum (spec 11.2)
                Ast.Def def = symbols.get(d.typeName().denotes());
                boolean hasEncoder = (def instanceof Ast.Data dd && dd.encoder().isPresent())
                        || (def instanceof Ast.SumData sd && sd.encoder().isPresent());
                if (!elemType.equals(Type.ref(d.typeName().denotes())) || !hasEncoder) {
                    throw elemEncMismatch(d.typeName().written(), elemType, pos);
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
