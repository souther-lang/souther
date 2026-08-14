package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.DeclarationMessage;
import souther.compiler.diag.msg.InvariantMessage;
import souther.compiler.diag.msg.BehaviorMessage;
import souther.compiler.diag.msg.TypeMessage;
import souther.compiler.diag.msg.CodecMessage;
import souther.compiler.diag.msg.DataMessage;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
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
    public record ConstCheck(String typeName, TypeSymbol type, Object value, SourcePos pos) {}

    /**
     * Every {@code 金額(constant)} in the module: a newtype construction whose argument folds to a
     * compile-time constant. The compiler runs each through the generated {@code $Ctfe.check}
     * (CTFE) so a violation becomes a compile error rather than a run-time abort (ADR-0032).
     *
     * <p>Desugared definitions, because that is what this finds them by. A construction is matched
     * as {@link Hir.NewData}, and a body that has not been desugared writes {@code 金額(500)} as an
     * application — so the walk matches nothing, the list comes back empty, and the compile goes on
     * with no check made and nothing said. Over a compile of the suite that is 174 constructions
     * found against 1: the state in the signature is what stops a caller handing over the bodies
     * from a rung below and being told the module is clean.
     */
    public static List<ConstCheck> constNewtypeChecks(List<Desugared.Fn> fns, Symbols symbols) {
        List<ConstCheck> out = new ArrayList<>();
        for (Desugared.Fn fn : fns) {
            collectConstChecks(fn.read().writtenBody(), symbols, out);
        }
        return out;
    }

    private static void collectConstChecks(Hir.Expr e, Symbols symbols, List<ConstCheck> out) {
        if (e instanceof Hir.NewData nd && !(nd.typeName() instanceof Hir.Name.Unanswered)
                && symbols.declarations().declaration(nd.typeName().denotes().key()) instanceof Hir.Data nt
                && nt.newtype() && isInvariantBearing(nd.typeName().denotes(), symbols)) {
            CallElaborator.newtypeConstantArg(nd).ifPresent(v ->
                    out.add(new ConstCheck(nd.typeName().written(), nd.typeName().denotes(), v, nd.pos())));
        }
        TypeChecker.forEachChild(e, c -> collectConstChecks(c, symbols, out));
    }

    public static boolean isInvariantBearing(TypeSymbol typeName, Symbols symbols) {
        return typeName != null && symbols.declarations().declaration(typeName.key()) instanceof Hir.Data d
                && !TypeOps.effectiveInvariants(d, symbols).isEmpty();
    }

    /**
     * No two clauses that apply to a data share a name. A spread carries the clauses of what it takes
     * in, names included, so the clash this reports is between a clause written here and one arriving
     * by spread as often as between two written here — and either way an arm naming it would answer
     * neither rule in particular.
     */
    private static void checkClauseNames(Hir.Data data, Symbols symbols) {
        Set<String> seen = new HashSet<>();
        for (Hir.InvariantClause clause : TypeOps.effectiveInvariants(data, symbols)) {
            String name = clause.name().orElse(null);
            if (name != null && !seen.add(name)) {
                throw CompileException.of(Diagnostic
                                .at(clause.pos()).say(new InvariantMessage.TwoClausesShareOneName(name, data.name())).build());
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
    public record Constructs(Map<TypeSymbol, String> originated, Map<TypeSymbol, String> carried) {

        public static Constructs empty() {
            return new Constructs(new LinkedHashMap<>(), new LinkedHashMap<>());
        }

        /** Whether {@code built} is built here at all, however it got here. */
        public boolean builds(TypeSymbol built) {
            return originated.containsKey(built) || carried.containsKey(built);
        }

        public Constructs copy() {
            return new Constructs(new LinkedHashMap<>(originated), new LinkedHashMap<>(carried));
        }

        /** The same set with everything counted as carried — what a body reached through something
         * it was handed rather than wrote, and so answers for none of. */
        public Constructs allCarried() {
            Map<TypeSymbol, String> all = new LinkedHashMap<>(carried);
            originated.forEach(all::putIfAbsent);
            return new Constructs(new LinkedHashMap<>(), all);
        }

        /** Takes on everything {@code other} builds, each kind staying the kind it is, and answers
         * whether that added anything. */
        public boolean absorb(Constructs other) {
            boolean added = false;
            for (Map.Entry<TypeSymbol, String> e : other.originated.entrySet()) {
                added |= originated.putIfAbsent(e.getKey(), e.getValue()) == null;
            }
            for (Map.Entry<TypeSymbol, String> e : other.carried.entrySet()) {
                added |= carried.putIfAbsent(e.getKey(), e.getValue()) == null;
            }
            return added;
        }
    }

    /**
     * The data types {@code e} constructs.
     *
     * <p>{@code bound} carries the names in scope, because a bare identifier is a unit data's
     * construction only when nothing has bound it — a local of the same name wins (spec §unit-data).
     * Without it, a parameter named after a unit data was read as constructing that unit.
     */
    static void collectConstructs(Hir.Expr e, Map<TypeSymbol, String> out, Symbols symbols,
                                  Map<String, Constructs> recConstructs) {
        Constructs all = Constructs.empty();
        collectConstructs(e, all, symbols, recConstructs);
        out.putAll(all.originated());
    }

    /** Whether {@code nd} arrived here already made, rather than being written here. */
    private static boolean carried(Hir.NewData nd, TypeSymbol built) {
        return nd.origin().carried(built);
    }

    static void collectConstructs(Hir.Expr e, Constructs out, Symbols symbols,
                                          Map<String, Constructs> recConstructs) {
        switch (e) {
            case Hir.LetIn li -> {
                collectConstructs(li.value(), out, symbols, recConstructs);
                collectConstructs(li.body(), out, symbols, recConstructs);
            }
            // An expansion builds what its arguments build and what the callee's body builds. What a
            // function argument builds is counted from the body, where the callee applies it; counted
            // here as well, one lambda's construction would be recorded twice.
            case Hir.Expansion ex -> {
                for (Hir.Bound b : ex.bound()) {
                    collectConstructs(b.value(), out, symbols, recConstructs);
                }
                collectConstructs(ex.body(), out, symbols, recConstructs);
            }
            case Hir.NewData nd -> {
                // A construction this body was handed is not this body's. It is handed one two ways.
                // A module's published value or helper carries its own: publishing the definition is
                // what states that origination, and the reader has no name to declare a type the
                // module keeps to itself by. What that does not cover is a type of some *other*
                // module the published body happened to build — that origination is neither the
                // reader's nor the publisher's to state, so it stays this behavior's to declare,
                // which it can. A value carries the construction its definition made, whatever module
                // declares the type: the definition is where the value is made, and a body that names
                // it compares against a limit rather than setting one.
                Map<TypeSymbol, String> side = carried(nd, nd.typeName().denotes())
                        ? out.carried() : out.originated();
                side.putIfAbsent(nd.typeName().denotes(), nd.typeName().name().quoted());
                for (Hir.FieldInit init : nd.inits()) {
                    collectConstructs(init.value(), out, symbols, recConstructs);
                }
            }
            case Hir.FieldAccess fa -> collectConstructs(fa.target(), out, symbols, recConstructs);
            case Hir.Tuple tup -> tup.elements().forEach(el -> collectConstructs(el, out, symbols, recConstructs));
            case Hir.TupleGet tg -> collectConstructs(tg.tuple(), out, symbols, recConstructs);
            case Hir.Apply call -> {
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
            case Hir.Binary bin -> {
                collectConstructs(bin.left(), out, symbols, recConstructs);
                collectConstructs(bin.right(), out, symbols, recConstructs);
            }
            case Hir.Neg neg -> collectConstructs(neg.operand(), out, symbols, recConstructs);
            case Hir.Match m -> {
                collectConstructs(m.scrutinee(), out, symbols, recConstructs);
                for (Hir.Case c : m.cases()) {
                    collectConstructs(c.body(), out, symbols, recConstructs);
                }
            }
            case Hir.If iff -> {
                collectConstructs(iff.cond(), out, symbols, recConstructs);
                collectConstructs(iff.then(), out, symbols, recConstructs);
                collectConstructs(iff.els(), out, symbols, recConstructs);
            }
            // an attempt builds the value on its success branch, so it needs the same permission a
            // plain construction does — what it does not do is abort when it fails
            case Hir.IfConstructed ic -> {
                collectConstructs(ic.construct(), out, symbols, recConstructs);
                collectConstructs(ic.then(), out, symbols, recConstructs);
                ic.els().forEach(arm ->
                        collectConstructs(arm.body(), out, symbols, recConstructs));
            }
            case Hir.ListLit lit -> lit.elements().forEach(el -> collectConstructs(el, out, symbols, recConstructs));
            case Hir.ListComp comp -> {
                collectConstructs(comp.element(), out, symbols, recConstructs);
                comp.guards().forEach(g -> collectConstructs(g, out, symbols, recConstructs));
            }
            // a block builds under the enclosing behavior's permission (spec §blocks)
            case Hir.Block block -> collectConstructs(block.body(), out, symbols, recConstructs);
            // a bare name that denotes a unit data is that unit's construction (spec §unit-data). Read off
            // what the name denotes rather than resolved again from its spelling: a reader with a
            // unit data spelled like the one another module's published body builds was recording
            // its own type as the one built. Carried or not is asked of the name for the same reason
            // it is asked of a construction node — it is the same question about the same thing.
            // `constructs` governs what this compilation declares; a unit the language gives
            // (`HALF_UP`) is vocabulary, not business data — as `None` is.
            case Hir.Var v when v.denotes() instanceof ValueName.OfType named
                    && symbols.declarations().declaredByCompilation(named.type().key())
                    && symbols.declarations().declaration(named.type().key()) instanceof Hir.UnitData -> {
                Map<TypeSymbol, String> side = named.origin().carried(named.type())
                        ? out.carried() : out.originated();
                side.putIfAbsent(named.type(), v.written().quoted());
            }
            case Hir.IntLit _ -> { }
            case Hir.DecimalLit _ -> { }
            case Hir.StringLit _ -> { }
            case Hir.BoolLit _ -> { }
            case Hir.Var _ -> { }
            // it builds nothing: no value is made where it stands
            case Hir.Unreachable _ -> { }
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
        return CompileException.of(Diagnostic.at(pos)
                .say(new DataMessage.NameIsListedMoreThanOnce(written, where))
                .build());
    }

    /**
     * As above for a list of type names. Two entries are the same when they denote one type, so
     * `Amount` an import brings in and `up.Amount` are the duplicate a spelling comparison misses.
     */
    static void rejectDuplicateTypes(List<Hir.Name> names, String where, SourcePos pos) {
        Set<TypeSymbol> seen = new HashSet<>();
        for (Hir.Name n : names) {
            // A name nothing declares denotes no type, so there is no type here for another to be
            // the same as. It was reported where it is written; calling it a duplicate as well
            // would be a second report about the one mistake.
            if (n instanceof Hir.Name.Unanswered) {
                continue;
            }
            if (!seen.add(n.denotes())) {
                throw duplicate(n.written(), where, pos);
            }
        }
    }

    /** Where to point at a field the data declares — the field's own name — or at the data header for
     * one that arrived through a {@code ...} spread, which is written in the data it came from. */
    private static Region fieldRegion(Hir.Data data, String field) {
        for (Hir.Field f : data.fields()) {
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
    private static List<String> sumCycle(TypeSymbol target, Symbols symbols,
                                         LinkedHashSet<TypeSymbol> path) {
        if (!(symbols.declarations().declaration(
                path.isEmpty() ? target.key() : last(path).key()) instanceof Hir.SumData s)) {
            return null;
        }
        for (Hir.Name caseName : s.cases()) {
            if (target.equals(caseName.denotes())) {
                List<String> out = new ArrayList<>();
                for (TypeSymbol seen : path) {
                    out.add(seen.name());
                }
                out.add(caseName.written());
                return out;
            }
            if (symbols.declarations().declaration(caseName.denotes().key()) instanceof Hir.SumData && path.add(caseName.denotes())) {
                List<String> found = sumCycle(target, symbols, path);
                if (found != null) {
                    return found;
                }
                path.remove(caseName.denotes());
            }
        }
        return null;
    }

    private static TypeSymbol last(LinkedHashSet<TypeSymbol> path) {
        TypeSymbol out = null;
        for (TypeSymbol t : path) {
            out = t;
        }
        return out;
    }

    static void checkSum(Hir.SumData sum, Symbols symbols) {
        rejectDuplicateTypes(sum.cases(), "the sum `" + sum.name() + "`", sum.pos());
        // A generated sum is a sealed interface, and its `permits` is settled when its own module is
        // generated — a case of another module cannot implement it, so it would be permitted without
        // being a member: no value satisfies the type and an exhaustive switch over it has no arms
        // (ADR-0057, the declared-sum counterpart of E1606).
        for (Hir.Name c : sum.cases()) {
            if (symbols.scope().isForeign(c.denotes())) {
                throw CompileException.of(Diagnostic
                                .at(c.name().reportedAt())
                                
                                .hint(new BehaviorMessage.ASumsCasesAreDeclaredWithIt(c.written())).say(new BehaviorMessage.ACaseIsDeclaredInAnotherModule(c.written(), sum.name(), c.denotes().module())).build());
            }
        }
        List<String> cycle = sumCycle(sum.declares(), symbols, new LinkedHashSet<>());
        if (cycle != null) {
            throw CompileException.of(Diagnostic
                            .at(sum.pos()).say(new BehaviorMessage.ASumContainsItself(sum.name(), String.join(" | ", cycle))).build());
        }
        sum.decoder().ifPresent(disc -> {
            // a derived codec dispatches over the leaves, so a nested sum's cases count too (§sum-data,
            // §sum-discrimination)
            Set<TypeSymbol> dispatchable = TypeOps.leafCases(Type.ref(sum.declares()), symbols);
            for (Hir.Variant v : disc.variants()) {
                Hir.Def caseDef = symbols.declarations().declaration(v.caseType().denotes().key());
                if (!dispatchable.contains(v.caseType().denotes())) {
                    throw CompileException.of(Diagnostic.at(v.pos())
                            .say(new CodecMessage.NotACaseOf(v.caseType().written(), sum.name()))
                            .build());
                }
                // a unit-data case has an implicit (field-less) decoder generated on its class;
                // a case may itself be a sum (spec §sum-data's nested `自社負担 | 先方負担`)
                boolean caseDecodes = caseDef instanceof Hir.UnitData
                        || (caseDef instanceof Hir.Data d && d.decoder().isPresent())
                        || (caseDef instanceof Hir.SumData s && s.decoder().isPresent());
                if (!caseDecodes) {
                    throw CompileException.of(Diagnostic.at(v.pos())
                            .say(new CodecMessage.CaseNeedsADecoder(v.caseType().written()))
                            .build());
                }
            }
        });
        sum.encoder().ifPresent(enc -> {
            // A case lays its fields flatly beside the discriminator the sum writes, so a case
            // declaring a field of that name and the tag want one key. Refused here rather than
            // written over where it is encoded, which would lose the value with nothing said.
            TypeSymbol carrying = TypeOps.memberCarryingField(
                    Type.ref(sum.declares()), enc.key(), symbols);
            if (carrying != null) {
                throw CompileException.of(Diagnostic
                                .at(sum.pos())
                                .hint(new DataMessage.TheTagAndTheFieldWantOneKey(enc.key())).say(new DataMessage.ACaseDeclaresTheDiscriminatorField(carrying.name(), enc.key(), sum.name())).build());
            }
            Set<TypeSymbol> covered = new HashSet<>();
            Set<TypeSymbol> encodable = TypeOps.leafCases(Type.ref(sum.declares()), symbols);
            for (Hir.EncVariant v : enc.variants()) {
                if (!encodable.contains(v.caseType().denotes())) {
                    throw CompileException.of(Diagnostic.at(v.pos())
                            .say(new CodecMessage.NotACaseOf(v.caseType().written(), sum.name()))
                            .build());
                }
                Hir.Def caseDef = symbols.declarations().declaration(v.caseType().denotes().key());
                boolean caseEncodes = caseDef instanceof Hir.UnitData
                        || (caseDef instanceof Hir.Data d && d.encoder().isPresent())
                        || (caseDef instanceof Hir.SumData s && s.encoder().isPresent());
                if (!caseEncodes) {
                    throw CompileException.of(Diagnostic.at(v.pos())
                            .say(new CodecMessage.CaseNeedsAnEncoder(v.caseType().written()))
                            .build());
                }
                covered.add(v.caseType().denotes());
            }
            for (TypeSymbol caseName : encodable) {
                if (!covered.contains(caseName)) {
                    throw CompileException.of(Diagnostic.at(enc.pos())
                            .say(new CodecMessage.TheEncoderIsMissingACase(sum.name(), caseName.name()))
                            .build());
                }
            }
        });
    }

    /**
     * The declarations of {@code module} that have no value, said of each group that has none of its
     * own.
     *
     * <p>Not a walk for a recursion with nowhere to stop. That is one of the ways a type comes to
     * have no value and reading for it was reading for the shape rather than for the answer: a sum
     * whose every case recurses has none, a set asked for more values than its element has has none,
     * and rules that cannot all hold leave none. All of them are one count coming to nothing.
     *
     * <p>What that count is and how it is reached is {@link TypeCardinality}; which of the
     * declarations with no value to say so about is {@link UninhabitableTypes}. What is left here is
     * saying it.
     */
    static List<CompileException> typesWithNoValue(List<Hir.Def> declarations, Symbols symbols) {
        List<CompileException> found = new ArrayList<>();
        for (List<TypeSymbol> group : UninhabitableTypes.withNoValueOfTheirOwn(declarations,
                TypeCardinality.solve(declarations, symbols))) {
            // The group is one thing to say and is said at the first of them the module declares.
            // Which one that is settles where the report sits and not what it is about: the others
            // have no value in the same way and for the same reason.
            Hir.Def at = (Hir.Def) symbols.declarations().declaration(group.get(0).key());
            found.add(CompileException.of(Diagnostic.at(at.pos())
                    .say(new DataMessage.DataCannotBeConstructed(at.name()))
                    .build()));
        }
        return found;
    }

    static void checkData(CheckContext ctx,
                                  Map<String, Type> recursiveHelperFns) {
        Map<String, Type> fields = TypeOps.fieldTypes(ctx.data(), ctx.symbols());

        // A newtype wraps one value and takes its representation, so there is nothing for it to be
        // when the value is absent. Whether a value is present is a property of the place it is
        // used, written there as `f: X?`. Read on the resolved type, so a data the author happens
        // to have named `Option` is an ordinary named data here.
        if (ctx.data().newtype() && fields.get("value") instanceof Type.OptionOf o) {
            throw CompileException.of(Diagnostic
                            .at(fieldRegion(ctx.data(), "value"))
                            
                            .hint(new DataMessage.WrapTheValueAndWriteTheQuestionMarkOnTheField(ctx.data().name())).say(new DataMessage.ANewtypeMayNotWrapAnOptional(ctx.data().name(), Type.show(o.element()))).build());
        }

        for (Map.Entry<String, Type> e : fields.entrySet()) {
            // A field is read through an accessor of the same name, and a data is a record over its
            // fields (spec §jvm-product). A no-argument method of Object is therefore taken: `toString` would
            // emit a second `toString()` and the class would not load, and the rest cannot be a record
            // component either. Reported here rather than left to codegen, as a duplicate name is.
            if (OBJECT_METHOD_NAMES.contains(e.getKey())) {
                throw CompileException.of(Diagnostic
                                .at(fieldRegion(ctx.data(), e.getKey()))
                                .say(new DataMessage.AFieldTakesAMethodOfObject(ctx.data().name(), e.getKey())).build());
            }
            if (TypeOps.withoutExternalForm(e.getValue(), ctx.symbols()) instanceof Type.TupleOf) {
                throw CompileException.of(Diagnostic
                                .at(fieldRegion(ctx.data(), e.getKey()))
                                .say(new DataMessage.ATupleCannotBeAField(ctx.data().name(), e.getKey())).build());
            }
            // A field is written to and read from the outside, so a map it holds is a JSON object and
            // its keys are strings. Inside a body the same map may be keyed by anything (ADR-0040).
            Type badKey = TypeOps.nonBoundaryMapKey(e.getValue(), ctx.symbols());
            if (badKey != null) {
                throw CompileException.of(Diagnostic
                                .at(fieldRegion(ctx.data(), e.getKey()))
                                
                                .hint(new TypeMessage.AMapIsAJsonObjectKeyedByStrings()).say(new TypeMessage.AFieldsMapCannotBeKeyedByThat(ctx.data().name() + "." + e.getKey(), Type.show(badKey))).build());
            }
        }

        for (Hir.InvariantClause clause : ctx.data().invariants()) {
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
                throw CompileException.of(Diagnostic.at(clause.expr().pos())
                                .say(new DeclarationMessage.AnInvariantExpressionIsBool(Type.show(t))).build());
            }
        }
        checkClauseNames(ctx.data(), ctx.symbols());

        ctx.data().decoder().ifPresent(dec -> checkDecoder(dec, ctx, fields));
        ctx.data().encoder().ifPresent(enc -> checkEncoder(enc, ctx));
    }

    private static Scope fieldScope(CheckContext ctx) {
        return fieldScope(ctx.data().declares(), ctx.data(), ctx.symbols());
    }

    /**
     * The bindings a declaration's own invariant reads: its fields, each as the binding it is.
     *
     * <p>{@code declared} is which declaration these fields belong to, which is not always the module
     * asking — the discharge check reads the clauses of types other modules declared. A field is
     * bound where it was written, so that is what the scope offers, and the clause carried in with the
     * declaration finds the very bindings it names.
     */
    static Scope fieldScope(TypeSymbol declared, Hir.Data data, Symbols symbols) {
        Map<String, Type> types = TypeOps.fieldTypes(data, symbols);
        Map<BindingId, Scope.Binding> bindings = new LinkedHashMap<>();
        TypeOps.fieldBindings(declared, data, symbols).forEach((name, binding) ->
                bindings.put(binding, new Scope.Binding(name, types.get(name))));
        return Scope.of(bindings);
    }

    private static void checkDecoder(Hir.DecoderDef dec, CheckContext ctx, Map<String, Type> fields) {
        switch (dec) {
            case Hir.PrimDecoder prim -> {
                Type inputType = TypeOps.primType(prim.from());
                Scope env = Scope.NONE.with(prim.input(), inputType);
                for (Hir.DecStmt stmt : prim.stmts()) {
                    switch (stmt) {
                        case Hir.Let let ->
                                env = env.with(let.binder(), Elaborator.typeOf(let.value(), env, ctx));
                    }
                }
                checkConstruct(prim.result(), ctx, fields, env);
            }
            case Hir.ObjectDecoder obj -> {
                Scope env = Scope.NONE;
                for (Hir.Bind bind : obj.binds()) {
                    env = env.with(bind.binder(), decRefType(bind.ref(), ctx.symbols()));
                }
                checkConstruct(obj.result(), ctx, fields, env);
            }
            case Hir.NewtypeDecoder nt -> {
                Scope env = Scope.NONE.with(nt.input(), decRefType(nt.inner(), ctx.symbols()));
                checkConstruct(nt.result(), ctx, fields, env);
            }
        }
    }

    /**
     * Whether a codec is there to be reached for (spec {@code [#a-codec-reached-for-exists]}).
     *
     * <p>Read of the declaration and not of a node on it. A unit data carries no derived decoder — it
     * has no field for one to read — and is decoded all the same, by the one its class is generated
     * with, which ignores its input and answers the single value there is. Reading the node refused a
     * field written from a unit data while the same type crossed a behavior's boundary, which is a
     * disagreement about the compiler's representation rather than about the model.
     *
     * <p>Whose vocabulary the name is, is asked before this and elsewhere
     * ({@code CrossingNominal}), so what is left here is the specification's other rule: a codec
     * named where none was derived and none was given.
     */
    private static boolean hasDecoder(Hir.Def def) {
        return switch (def) {
            case Hir.Data d -> d.decoder().isPresent();
            case Hir.SumData s -> s.decoder().isPresent();
            case Hir.UnitData _ -> true;
            case null -> false;
        };
    }

    /** As {@link #hasDecoder}, for the other direction. */
    private static boolean hasEncoder(Hir.Def def) {
        return switch (def) {
            case Hir.Data d -> d.encoder().isPresent();
            case Hir.SumData s -> s.encoder().isPresent();
            case Hir.UnitData _ -> true;
            case null -> false;
        };
    }

    private static Type decRefType(Hir.DecRef ref, Symbols symbols) {
        return switch (ref) {
            case Hir.SetDecRef s -> Type.set(decRefType(s.element(), symbols));
            case Hir.PrimDecRef p -> TypeOps.primType(p.kind());
            case Hir.DataDecRef d -> {
                if (!hasDecoder(symbols.declarations().declaration(d.typeName().denotes().key()))) {
                    throw CompileException.of(Diagnostic.at(d.pos())
                            .say(new CodecMessage.HasNoDecoder(d.typeName().written()))
                            .build());
                }
                yield Type.ref(d.typeName().denotes());
            }
            case Hir.ListDecRef l -> Type.list(decRefType(l.element(), symbols));
            case Hir.OptionDecRef o -> Type.option(decRefType(o.element(), symbols));
            case Hir.MapDecRef mp -> Type.map(mp.key().type(), decRefType(mp.value(), symbols));
        };
    }

    private static void checkConstruct(Hir.Construct c, CheckContext ctx, Map<String, Type> fields,
                                       Scope env) {
        if (!c.typeName().denotes().equals(ctx.data().declares())) {
            throw CompileException.of(Diagnostic.at(c.pos())
                    .say(new CodecMessage.TheDecoderBuildsAnotherType(ctx.data().name(),
                            c.typeName().written()))
                    .build());
        }
        // a decoder's construction gives every field a value of its own; nothing builds one with a
        // spread, so there is no binding to copy from here
        checkConstruction(c.typeName().written(), c.inits(), List.of(), c.pos(), fields, env, ctx);
    }

    /**
     * What each declared field of a construction is given, in declaration order — the one place that
     * answers it. A field written out is given what was written; one no field init names is given the
     * read of that field off the value spread into the construction, which is a field read like the
     * one an author writes. So a construction carries no spread past here, and every reader of it
     * asks the same values in the same order rather than working the spread out again.
     *
     * <p>Where several spreads carry one field, the first of them supplies it — one field is given
     * one value, and which is decided here and not by whichever reader looks.
     */
    static List<Core.FieldValue> checkConstruction(String typeName, List<Hir.FieldInit> inits,
                                          List<Core.Read> spreads,
                                          SourcePos pos, Map<String, Type> fields, Scope env,
                                          CheckContext ctx) {
        Map<String, Core.FieldValue> written = new LinkedHashMap<>();
        for (Hir.FieldInit init : inits) {
            if (written.containsKey(init.name())) {
                throw CompileException.of(Diagnostic.at(init.pos())
                        .say(new DataMessage.FieldIsDefinedMoreThanOnce(init.name()))
                        .build());
            }
            Type ft = fields.get(init.name());
            if (ft == null) {
                throw CompileException.of(Diagnostic.at(init.written().reportedAt())
                        .say(new DataMessage.NotAFieldOf(init.name(), typeName))
                        .build());
            }
            // push the field's declared type into the value expression, so a field initialised from a
            // fold over an empty-collection seed has its result pinned by the field type (issue #70).
            // This is also the one place an optional may be made (ADR-0011), which the context carries
            // rather than the expected type: a model may write `Option<T>` where it reads one, so an
            // expected optional no longer means a field asked for it (issue #202).
            CheckContext making = ctx.makingAnOptional(ft instanceof Type.OptionOf);
            Core value = Elaborator.liftIntoOption(
                    Elaborator.elaborate(init.value(), env, making, ft), ft, ctx.symbols());
            written.put(init.name(), new Core.FieldValue(init.name(), value, init.pos()));
            Type vt = value.type();
            // a case value widens to its sum-typed field (spec §sum-data)
            if (!TypeOps.assignable(vt, ft, ctx.symbols())) {
                throw CompileException.of(Diagnostic
                                .at(init.written().reportedAt())
                                
                                .diff(Type.show(vt, ft), Type.show(ft, vt)).say(new DataMessage.AFieldExpectsAnotherType(init.name(), Type.show(ft), Type.show(vt))).build());
            }
        }
        // the sums spread here, which a field the construction still wants was not in the shared part
        // of — all of them, because naming one of several would pick by position and send the author
        // to open a sum whose cases never had the field
        Set<String> fromSums = new LinkedHashSet<>();
        List<Spread> spread = new ArrayList<>();
        for (Core.Read read : spreads) {
            String sp = read.name();
            Type bound = env.typeOf(read.binding());
            if (bound instanceof Type.Ref ref
                    && ctx.symbols().declarations().declaration(ref.name().key()) instanceof Hir.SumData sum) {
                fromSums.add(Type.show(bound));
                spread.add(new Spread(read, spreadOfSum(sp, sum, bound, pos, ctx)));
            } else if (bound instanceof Type.Ref ref
                    && ctx.symbols().declarations().declaration(ref.name().key()) instanceof Hir.Data sd) {
                spread.add(new Spread(read, TypeOps.fieldTypes(sd, ctx.symbols())));
            } else {
                Diagnostic.Builder d = Diagnostic.at(pos)
                        .say(new DataMessage.SpreadIsNotADataValue(sp));
                if (bound instanceof Type.Union) {
                    d = d.hint(new DataMessage.NameTheUnionWithADeclaration(sp));
                }
                throw CompileException.of(d.build());
            }
        }
        List<Core.FieldValue> values = new ArrayList<>();
        for (Map.Entry<String, Type> f : fields.entrySet()) {
            Core.FieldValue own = written.get(f.getKey());
            if (own != null) {
                values.add(own);
                continue;
            }
            Spread from = supplying(spread, f.getKey());
            if (from == null) {
                Diagnostic.Builder d = Diagnostic.at(pos)
                        .say(new DataMessage.ConstructionIsMissingAField(typeName, f.getKey()));
                // one rule broken in one of several ways, and the hint is where the way is said. What
                // was written decides it: `fromSums` counts the sums spread, which says nothing about
                // whether anything was spread at all, so a construction with no spread is asked about
                // separately rather than read off an empty count.
                if (spreads.isEmpty()) {
                    d = d.hint(new DataMessage.GiveTheFieldAValue(f.getKey()));
                } else {
                    d = switch (fromSums.size()) {
                        case 0 -> d.hint(new DataMessage.SupplyTheFieldExplicitly(f.getKey()));
                        case 1 -> d.hint(new DataMessage.TheFieldIsNotInWhatTheSumShares(
                                f.getKey(), fromSums.iterator().next()));
                        default -> d.hint(new DataMessage.TheFieldIsInTheSharedPartOfNoneOfThese(
                                f.getKey(), String.join(", ", fromSums)));
                    };
                }
                throw CompileException.of(d.build());
            }
            Type pv = from.fields().get(f.getKey());
            if (!TypeOps.assignable(pv, f.getValue(), ctx.symbols())) {
                throw CompileException.of(Diagnostic.at(pos)
                        .say(new DataMessage.SpreadSuppliesTheWrongType(f.getKey(), Type.show(pv),
                                typeName, Type.show(f.getValue())))
                        .diff(Type.show(pv, f.getValue()), Type.show(f.getValue(), pv)).build());
            }
            // The value is read at the type the source declares the field, which is the type the
            // backend loads it at; that it fits the field being given it was decided just above.
            values.add(new Core.FieldValue(f.getKey(),
                    new Core.FieldAccess(from.read(), f.getKey(), pv, from.read().pos()),
                    from.read().pos()));
        }
        return values;
    }

    /** A value a construction spreads, and the fields it carries. */
    private record Spread(Core.Read read, Map<String, Type> fields) {}

    /** The first of {@code spreads} carrying {@code field}, or null where none does. */
    private static Spread supplying(List<Spread> spreads, String field) {
        for (Spread s : spreads) {
            if (s.fields().containsKey(field)) {
                return s;
            }
        }
        return null;
    }

    /** What a spread of a sum copies: the fields of the data every one of its cases spreads. This is
     * the construction side of reading such a field off the sum, and takes its shared part from the
     * same place the read does, so the two answer alike. A sum whose cases share no spread has nothing
     * to copy — cases that merely declare a field of the same name have not shared it — and that is
     * reported here rather than left to the missing-field report, which would name a field the author
     * can see in every case. */
    private static Map<String, Type> spreadOfSum(String name, Hir.SumData sum, Type bound,
                                                 SourcePos pos, CheckContext ctx) {
        Map<String, Type> shared = TypeOps.commonSpreadFields(sum, ctx.symbols());
        if (shared.isEmpty()) {
            throw CompileException.of(Diagnostic.at(pos)
                    .say(new DataMessage.SpreadOfASumWhoseCasesShareNothing(name, Type.show(bound)))
                    .build());
        }
        return shared;
    }

    private static void checkEncoder(Hir.EncoderDef enc, CheckContext ctx) {
        Scope env = Scope.NONE.with(enc.self(), Type.ref(ctx.data().declares()));
        checkRawExpr(enc.result(), env, ctx);
    }

    private static void checkRawExpr(Hir.RawExpr raw, Scope env, CheckContext ctx) {
        switch (raw) {
            case Hir.TextRaw t -> Elaborator.requireType(t.arg(), Type.STRING, env, ctx,
                    "argument of Text");
            case Hir.IntRaw i -> Elaborator.requireType(i.arg(), Type.INT, env, ctx,
                    "argument of Int");
            case Hir.BoolRaw b -> Elaborator.requireType(b.arg(), Type.BOOL, env, ctx,
                    "argument of Bool");
            case Hir.DecimalRaw d -> Elaborator.requireType(d.arg(), Type.DECIMAL, env, ctx,
                    "argument of Decimal");
            case Hir.IsoTextRaw t -> {
                Type at = Elaborator.typeOf(t.arg(), env, ctx);
                // Asked of each primitive, so a temporal added later is admitted where it is
                // declared rather than being refused here by a comparison written before it existed.
                boolean temporal = at instanceof Type.Prim p && switch (p) {
                    case DATE, TIME, DATETIME, INSTANT -> true;
                    case INT, STRING, BOOL, DECIMAL, RAW -> false;
                };
                if (!temporal) {
                    throw CompileException.of(Diagnostic.at(t.pos())
                            .say(new CodecMessage.AnIsoTextEncoderTakesATemporalValue(Type.show(at)))
                            .build());
                }
            }
            case Hir.OptionRaw o -> {
                Type at = Elaborator.typeOf(o.access(), env, ctx);
                if (!(at instanceof Type.OptionOf oo)) {
                    throw CompileException.of(Diagnostic.at(o.pos())
                            .say(new CodecMessage.AnOptionalEncoderTakesAnOptional(Type.show(at)))
                            .build());
                }
                checkRawExpr(o.inner(), env.with(o.elem(), oo.element()), ctx);
            }
            case Hir.ObjectRaw o -> {
                for (Hir.RawEntry entry : o.entries()) {
                    checkRawExpr(entry.value(), env, ctx);
                }
            }
            case Hir.EncodeRaw e -> {
                if (!hasEncoder(ctx.symbols().declarations()
                        .declaration(e.typeName().denotes().key()))) {
                    throw CompileException.of(Diagnostic.at(e.pos())
                            .say(new CodecMessage.HasNoEncoder(e.typeName().written()))
                            .build());
                }
                Elaborator.requireType(e.arg(), Type.ref(e.typeName().denotes()), env, ctx,
                        "argument of " + e.typeName().written() + ".encode");
            }
            case Hir.ListEnc le -> {
                Type st = Elaborator.typeOf(le.source(), env, ctx);
                if (!(st instanceof Type.ListOf lo)) {
                    throw CompileException.of(Diagnostic.at(le.pos())
                            .say(new CodecMessage.AListEncoderTakesAList(Type.show(st)))
                            .build());
                }
                checkEncElem(le.elem(), lo.element(), le.pos(), ctx.symbols());
            }
            case Hir.SetEnc se -> {
                Type st = Elaborator.typeOf(se.source(), env, ctx);
                if (!(st instanceof Type.SetOf so)) {
                    throw CompileException.of(Diagnostic.at(se.pos())
                            .say(new CodecMessage.ASetEncoderTakesASet(Type.show(st)))
                            .build());
                }
                checkEncElem(se.elem(), so.element(), se.pos(), ctx.symbols());
            }
            case Hir.MapEnc me -> {
                Type st = Elaborator.typeOf(me.source(), env, ctx);
                if (!(st instanceof Type.MapOf mo)) {
                    throw CompileException.of(Diagnostic.at(me.pos())
                            .say(new CodecMessage.AMapEncoderTakesAMap(Type.show(st)))
                            .build());
                }
                checkEncElem(me.elem(), mo.value(), me.pos(), ctx.symbols());
            }
        }
    }

    private static void checkEncElem(Hir.EncElem elem, Type elemType, SourcePos pos,
                                     Symbols symbols) {
        switch (elem) {
            case Hir.PrimEnc p -> {
                if (!elemType.equals(TypeOps.primType(p.kind()))) {
                    throw elemEncMismatch(Type.show(TypeOps.primType(p.kind())), elemType, pos);
                }
            }
            case Hir.DataEnc d -> {
                // the element may be a product or a sum: `List<事前承認理由>` holds a sum (spec §encoder-derivation)
                Hir.Def def = symbols.declarations().declaration(d.typeName().denotes().key());
                boolean hasEncoder = (def instanceof Hir.Data dd && dd.encoder().isPresent())
                        || (def instanceof Hir.SumData sd && sd.encoder().isPresent());
                if (!elemType.equals(Type.ref(d.typeName().denotes())) || !hasEncoder) {
                    throw elemEncMismatch(d.typeName().written(), elemType, pos);
                }
            }
            // a collection element is itself a collection: descend both the encoder and the type
            case Hir.ListElemEnc l -> {
                if (!(elemType instanceof Type.ListOf lo)) {
                    throw elemEncMismatch("List", elemType, pos);
                }
                checkEncElem(l.elem(), lo.element(), pos, symbols);
            }
            case Hir.SetElemEnc s -> {
                if (!(elemType instanceof Type.SetOf so)) {
                    throw elemEncMismatch("Set", elemType, pos);
                }
                checkEncElem(s.elem(), so.element(), pos, symbols);
            }
            case Hir.MapElemEnc m -> {
                if (!(elemType instanceof Type.MapOf mo)) {
                    throw elemEncMismatch("Map", elemType, pos);
                }
                checkEncElem(m.value(), mo.value(), pos, symbols);
            }
            // an absent member is written null, so the element encoder is one level above what the
            // option holds, as the type is
            case Hir.OptionElemEnc o -> {
                if (!(elemType instanceof Type.OptionOf oo)) {
                    throw elemEncMismatch("Option", elemType, pos);
                }
                checkEncElem(o.elem(), oo.element(), pos, symbols);
            }
        }
    }

    /** The element encoder and the element type disagree, both named as they are written — the
     * encoder by the type it encodes (`String`, `商品ID`, `List`), the element by {@link Type#show}. */
    private static CompileException elemEncMismatch(String encoder, Type elemType, SourcePos pos) {
        return CompileException.of(Diagnostic.at(pos)
                .say(new CodecMessage.TheElementEncoderIsNotForTheElementType(
                        "`" + encoder + "`", Type.show(elemType)))
                .build());
    }

}
