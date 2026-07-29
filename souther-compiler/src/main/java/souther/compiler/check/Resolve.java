package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.types.ValueName;
import souther.compiler.Prelude;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Says once, for a whole module, what every written type name denotes.
 *
 * <p>Before this pass a name is a spelling: {@code 金額}, {@code billing.金額}, or an alias'd
 * {@code B.金額}, and whether the three mean one type is a question each consumer used to answer for
 * itself — which is why a capability reached the positions someone wired it to and no others
 * (issues #101, #113, #124, #132, #154). After it, every {@link Ast.Name} in the tree carries the
 * {@link TypeName} it denotes, and a check that wants to know whether two names are the same type
 * compares what they denote. There is no spelling left to compare.
 *
 * <p>A name that denotes nothing is reported here and denotes {@link TypeName#unresolved} — which
 * becomes {@link souther.compiler.types.Type#ERRONEOUS} — so no later pass sees an unresolved name
 * and none of them needs a null branch. The pass does not stop: the rest of the module is resolved
 * as if the mistake were not there, which is what lets an author be told about every unknown name at
 * once and lets an editor still say what the names around one mean. A name a pass synthesized
 * already knowing what it means (a codec {@code Deriver} builds from a field's type) is left as it
 * is.
 */
public final class Resolve {

    private final Symbols symbols;
    private final Values values;
    /** Every name this pass answered, in the order it met them. */
    private final List<Denotation> denotations = new ArrayList<>();
    /** The same, for the names used as values. */
    private final List<ValueUse> values0 = new ArrayList<>();
    /** Every name it could not answer, as the error it would once have thrown. */
    private final List<CompileException> unresolved = new ArrayList<>();

    private Resolve(Symbols symbols, Values values) {
        this.symbols = symbols;
        this.values = values;
    }

    /**
     * What a module can name in the value namespace without a binding: its own helpers, and the
     * behaviors it can reach.
     *
     * <p>The behaviors come from outside — an import brings one in — so they are given rather than
     * read off the module. A module resolved on its own reaches only what it declares.
     */
    public record Values(String module, Map<String, ValueName.Helper> helpers,
                         Map<String, ValueName.Behavior> behaviors) {

        /** What a module reaches when nothing else is in sight. */
        public static Values of(Ast.Module m) {
            Map<String, ValueName.Helper> helpers = new LinkedHashMap<>();
            for (String helper : HelperInliner.helpersOf(m).keySet()) {
                helpers.put(helper, new ValueName.Helper(m.name(), helper));
            }
            Map<String, ValueName.Behavior> behaviors = new LinkedHashMap<>();
            for (Ast.BehaviorDef b : m.behaviors()) {
                behaviors.put(b.name(), new ValueName.Behavior(m.name(), b.name()));
            }
            return new Values(m.name(), helpers, behaviors);
        }
    }

    /**
     * One written name and what it turned out to denote, where it was written.
     *
     * <p>This is the pass's other product. Working out what a name means is a traversal of the whole
     * module, and an editor asking "what is under the cursor" or "where else is this named" is asking
     * about the answers that traversal already gave. Collecting them here is what keeps the editor
     * from walking the tree again with a rule of its own — which, before this, is how renaming a
     * type could rewrite the tail of a qualified reference to a different module's type.
     *
     * @param written the name as the source wrote it, bare or qualified
     * @param denotes what it names
     * @param pos where the written name starts
     */
    public record Denotation(String written, TypeName denotes, SourcePos pos) {}

    /**
     * One written name in the value namespace and what it turned out to denote, where it was
     * written. What {@link Denotation} is for a type, and collected for the same reason: an editor
     * asking what is under the cursor is asking about the answer this traversal already gave.
     */
    public record ValueUse(String written, ValueName denotes, SourcePos pos) {}

    /**
     * A resolved module, every name the pass answered in it, and the names it could not answer.
     *
     * <p>A name that denotes nothing does not end the pass. It denotes {@link TypeName#unresolved},
     * which becomes {@link souther.compiler.types.Type#ERRONEOUS}, and the rest of the module is
     * resolved as if the mistake were not there — so an author is told about every unknown name at
     * once instead of one per compile, and an editor can still say what the names around it mean.
     */
    public record Resolved(Ast.Module module, List<Denotation> denotations, List<ValueUse> values,
                           List<CompileException> unresolved) {}

    /** {@code m} with every name it writes resolved against its own definitions — a module compiled
     * with nothing else in sight. */
    public static Ast.Module module(Ast.Module m) {
        return module(m, TypeChecker.symbols(m));
    }

    /** {@code m} with every name it writes resolved against {@code symbols}. */
    public static Ast.Module module(Ast.Module m, Symbols symbols) {
        Resolved resolved = resolving(m, symbols);
        if (!resolved.unresolved().isEmpty()) {
            // This entry point answers with a module or not at all, which is what its one caller —
            // loading the shipped core — needs: a misspelled type in a prelude resource is a fault in
            // the compiler, not something an author can be told about and carry on past.
            throw resolved.unresolved().get(0);
        }
        return resolved.module();
    }

    /** As {@link #module(Ast.Module, Symbols)}, keeping what each name was answered with. */
    public static Resolved resolving(Ast.Module m, Symbols symbols) {
        return resolving(m, symbols, Values.of(m));
    }

    /** As {@link #resolving(Ast.Module, Symbols)}, with what the module reaches in the value
     * namespace given rather than read off the module itself. */
    public static Resolved resolving(Ast.Module m, Symbols symbols, Values values) {
        Resolve r = new Resolve(symbols, values);
        List<Ast.Def> defs = new ArrayList<>();
        for (Ast.Def def : m.defs()) {
            defs.add(r.def(def));
        }
        List<Ast.BehaviorDef> behaviors = new ArrayList<>();
        for (Ast.BehaviorDef b : m.behaviors()) {
            behaviors.add(switch (b) {
                case Ast.SpecBehavior spec -> new Ast.SpecBehavior(spec.name(), r.params(spec.params()),
                        r.retType(spec.ret()), r.names(spec.constructs()), spec.dependsOn(), spec.pos());
                case Ast.PipeBehavior pipe -> new Ast.PipeBehavior(pipe.name(), pipe.stages(),
                        r.retType(pipe.declaredOut()), pipe.pos());
            });
        }
        List<Ast.FnDef> fns = new ArrayList<>();
        for (Ast.FnDef fn : m.fns()) {
            fns.add(r.fn(fn));
        }
        List<Ast.Example> examples = new ArrayList<>();
        for (Ast.Example e : m.examples()) {
            List<Ast.ExampleRow> rows = new ArrayList<>();
            for (Ast.ExampleRow row : e.rows()) {
                List<Ast.With> withs = new ArrayList<>();
                for (Ast.With w : row.withs()) {
                    withs.add(new Ast.With(w.dep(), r.expr(w.value()), w.pos()));
                }
                rows.add(new Ast.ExampleRow(row.description(), r.exprs(row.inputs()), withs,
                        r.expr(row.expected()), row.pos()));
            }
            examples.add(new Ast.Example(e.target(), rows, e.pos()));
        }
        List<Ast.Fake> fakes = new ArrayList<>();
        for (Ast.Fake f : m.fakes()) {
            List<Ast.FakeRow> rows = new ArrayList<>();
            for (Ast.FakeRow row : f.rows()) {
                rows.add(new Ast.FakeRow(row.inputs() == null ? null : r.exprs(row.inputs()),
                        r.expr(row.output()), row.isDefault(), row.pos()));
            }
            fakes.add(new Ast.Fake(f.target(), rows, f.pos()));
        }
        Map<String, Ast.RetType> exposedOutputs = new LinkedHashMap<>();
        for (Map.Entry<String, Ast.RetType> e : m.exposedOutputs().entrySet()) {
            exposedOutputs.put(e.getKey(), r.retType(e.getValue()));
        }
        return new Resolved(
                new Ast.Module(m.name(), m.exposing(), exposedOutputs, m.imports(), defs,
                        behaviors, fns, examples, fakes, m.exampleFileTarget(), m.pos()),
                List.copyOf(r.denotations), List.copyOf(r.values0), List.copyOf(r.unresolved));
    }

    private Ast.FnDef fn(Ast.FnDef f) {
        List<Ast.FnParam> params = new ArrayList<>();
        Bindings bound = Bindings.NONE;
        for (Ast.FnParam p : f.params()) {
            params.add(new Ast.FnParam(p.name(), paramType(p.type()), p.typeFromPattern(), p.pos()));
            bound = bound.and(p.name(), p.pos());
        }
        return new Ast.FnDef(f.name(), params, retType(f.declaredReturn()), f.intrinsicKey(),
                f.body() == null ? null : expr(f.body(), bound), f.partial(), f.pos());
    }

    // --- written types ---

    private List<Ast.Param> params(List<Ast.Param> params) {
        List<Ast.Param> out = new ArrayList<>();
        for (Ast.Param p : params) {
            out.add(new Ast.Param(p.name(), retType(p.type()), p.pos()));
        }
        return out;
    }

    private List<Ast.Field> fields(List<Ast.Field> fields) {
        List<Ast.Field> out = new ArrayList<>();
        for (Ast.Field f : fields) {
            out.add(new Ast.Field(f.name(), typeRef(f.type()), f.pos()));
        }
        return out;
    }

    private Ast.ParamType paramType(Ast.ParamType t) {
        return switch (t) {
            case null -> null;
            case Ast.RetType rt -> retType(rt);
            case Ast.FnType ft -> {
                List<Ast.RetType> ps = new ArrayList<>();
                for (Ast.RetType p : ft.params()) {
                    ps.add(retType(p));
                }
                yield new Ast.FnType(ps, retType(ft.result()), ft.pos());
            }
        };
    }

    private Ast.RetType retType(Ast.RetType ret) {
        if (ret == null) {
            return null;
        }
        List<Ast.TypeRef> cases = new ArrayList<>();
        for (Ast.TypeRef c : ret.cases()) {
            cases.add(typeRef(c));
        }
        return new Ast.RetType(cases, ret.pos());
    }

    /** A written type reference, with what it denotes decided here — once, and in the module that
     * wrote it, so no later reader has to know where it was written. */
    private Ast.TypeRef typeRef(Ast.TypeRef ref) {
        if (ref == null || ref.denotes() != null) {
            return ref;
        }
        Ast.TypeRef arg = typeRef(ref.arg());
        List<Ast.TypeRef> elems = null;
        if (ref.tupleElems() != null) {
            elems = new ArrayList<>();
            for (Ast.TypeRef e : ref.tupleElems()) {
                elems.add(typeRef(e));
            }
        }
        Ast.TypeRef resolved = new Ast.TypeRef(ref.name(), arg, elems, ref.pos());
        Ast.TypeRef denoted = resolved.denoting(typeOf(resolved));
        // A reference with no name is a tuple or a container shape, which names no declaration.
        if (denoted.name() != null && denoted.pos() != null) {
            TypeName names = symbols.resolve(denoted.name());
            if (names != null) {
                denotations.add(new Denotation(denoted.name(), names, denoted.pos()));
            }
        }
        return denoted;
    }

    // --- definitions ---

    private Ast.Def def(Ast.Def def) {
        return switch (def) {
            case Ast.UnitData u -> u;
            // an invariant reads the fields of the data it belongs to, which are what bind its
            // names — `value > 0` is about this declaration's `value`, whatever else is in scope
            case Ast.Data d -> new Ast.Data(d.name(), d.newtype(), names(d.includes()), fields(d.fields()),
                    d.invariant().map(inv -> expr(inv, boundFields(d))), d.decoder().map(this::decoder),
                    d.encoder().map(this::encoder), d.pos());
            case Ast.SumData s -> new Ast.SumData(s.name(), sumCases(s), s.decoder().map(this::discriminate),
                    s.encoder().map(this::sumEncoder), s.pos());
        };
    }

    /** A sum's cases keep their own message: {@code data X = A | B} names the cases of one type, so a
     * name nothing declares is answered against that sum rather than as a bare unknown type. */
    private List<Ast.Name> sumCases(Ast.SumData s) {
        List<Ast.Name> out = new ArrayList<>();
        for (Ast.Name c : s.cases()) {
            if (c.denotes() != null) {
                out.add(c);
                continue;
            }
            TypeName denoted = symbols.resolve(c.written());
            if (denoted == null) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.sum.unknowncase").title("check.sum.title")
                                .at(s.pos()).args(c.written(), s.name()).build(),
                        "unknown case `" + c.written() + "` in sum `" + s.name() + "`");
            }
            out.add(c.denoting(denoted));
        }
        return out;
    }

    /**
     * The fields of a declaration, as the names its own invariant reads — the ones written here and
     * the ones a spread brings in, which are as much this declaration's fields as the written ones
     * (and are what a spread-in invariant was written against).
     */
    private Bindings boundFields(Ast.Data d) {
        return boundFields(d, Bindings.NONE, new LinkedHashSet<>());
    }

    private Bindings boundFields(Ast.Data d, Bindings bound, Set<TypeName> spread) {
        for (Ast.Field f : d.fields()) {
            bound = bound.and(f.name(), f.pos());
        }
        for (Ast.Name include : d.includes()) {
            TypeName source = include.denotes() != null
                    ? include.denotes() : symbols.resolve(include.written());
            // a spread of a spread reaches the fields underneath; a spread that names nothing, or
            // names its way back round, is reported where the declaration is checked
            if (source != null && spread.add(source)
                    && symbols.get(source) instanceof Ast.Data src) {
                bound = boundFields(src, bound, spread);
            }
        }
        return bound;
    }

    private Ast.Discriminate discriminate(Ast.Discriminate d) {
        List<Ast.Variant> variants = new ArrayList<>();
        for (Ast.Variant v : d.variants()) {
            variants.add(new Ast.Variant(v.tag(), type(v.caseType()), v.pos()));
        }
        return new Ast.Discriminate(d.key(), variants, d.pos());
    }

    private Ast.SumEncoder sumEncoder(Ast.SumEncoder e) {
        List<Ast.EncVariant> variants = new ArrayList<>();
        for (Ast.EncVariant v : e.variants()) {
            variants.add(new Ast.EncVariant(type(v.caseType()), v.tag(), v.pos()));
        }
        return new Ast.SumEncoder(e.key(), variants, e.pos());
    }

    // --- decoders ---

    /** A decoder reads the value it is decoding under the name it gives it, and an object decoder
     * reads what each of its binds took out of the object. Those are what bind its names. */
    private Ast.DecoderDef decoder(Ast.DecoderDef d) {
        return switch (d) {
            case Ast.PrimDecoder p -> {
                Bindings bound = Bindings.NONE.and(p.inputName(), p.pos());
                List<Ast.DecStmt> stmts = new ArrayList<>();
                for (Ast.DecStmt s : p.stmts()) {
                    if (s instanceof Ast.Let let) {
                        stmts.add(new Ast.Let(let.name(), expr(let.value(), bound), let.pos()));
                        bound = bound.and(let.name(), let.pos());
                    } else {
                        stmts.add(s);
                    }
                }
                yield new Ast.PrimDecoder(p.from(), p.inputName(), stmts,
                        construct(p.result(), bound), p.pos());
            }
            case Ast.ObjectDecoder o -> {
                List<Ast.Bind> binds = new ArrayList<>();
                Bindings bound = Bindings.NONE;
                for (Ast.Bind b : o.binds()) {
                    binds.add(new Ast.Bind(b.name(), b.key(), decRef(b.ref()), b.pos()));
                    bound = bound.and(b.name(), b.pos());
                }
                yield new Ast.ObjectDecoder(binds, construct(o.result(), bound), o.pos());
            }
            case Ast.NewtypeDecoder n -> new Ast.NewtypeDecoder(decRef(n.inner()), n.inputName(),
                    construct(n.result(), Bindings.NONE.and(n.inputName(), n.pos())), n.pos());
        };
    }

    private Ast.DecRef decRef(Ast.DecRef ref) {
        return switch (ref) {
            case Ast.PrimDecRef p -> p;
            case Ast.DataDecRef d -> new Ast.DataDecRef(type(d.typeName()), d.pos());
            case Ast.ListDecRef l -> new Ast.ListDecRef(decRef(l.element()), l.pos());
            case Ast.SetDecRef s -> new Ast.SetDecRef(decRef(s.element()), s.pos());
            case Ast.OptionDecRef o -> new Ast.OptionDecRef(decRef(o.element()), o.pos());
            case Ast.MapDecRef m -> new Ast.MapDecRef(decRef(m.value()), decRef(m.key()), m.pos());
        };
    }

    private Ast.Construct construct(Ast.Construct c, Bindings bound) {
        List<Ast.FieldInit> inits = new ArrayList<>();
        for (Ast.FieldInit i : c.inits()) {
            inits.add(new Ast.FieldInit(i.name(), expr(i.value(), bound), i.pos()));
        }
        return new Ast.Construct(type(c.typeName()), inits, c.spreads(), c.pos());
    }

    // --- encoders ---

    /** An encoder reads the value it is encoding under the name it gives it. */
    private Ast.EncoderDef encoder(Ast.EncoderDef e) {
        return new Ast.EncoderDef(e.selfName(),
                rawExpr(e.result(), Bindings.NONE.and(e.selfName(), e.pos())), e.pos());
    }

    private Ast.RawExpr rawExpr(Ast.RawExpr r, Bindings bound) {
        return switch (r) {
            case Ast.TextRaw t -> new Ast.TextRaw(expr(t.arg(), bound), t.pos());
            case Ast.IntRaw i -> new Ast.IntRaw(expr(i.arg(), bound), i.pos());
            case Ast.BoolRaw b -> new Ast.BoolRaw(expr(b.arg(), bound), b.pos());
            case Ast.DecimalRaw d -> new Ast.DecimalRaw(expr(d.arg(), bound), d.pos());
            case Ast.IsoTextRaw i -> new Ast.IsoTextRaw(expr(i.arg(), bound), i.pos());
            case Ast.EncodeRaw en ->
                    new Ast.EncodeRaw(type(en.typeName()), expr(en.arg(), bound), en.pos());
            case Ast.ListEnc l -> new Ast.ListEnc(expr(l.source(), bound), encElem(l.elem()), l.pos());
            case Ast.SetEnc s -> new Ast.SetEnc(expr(s.source(), bound), encElem(s.elem()), s.pos());
            case Ast.MapEnc m -> new Ast.MapEnc(expr(m.source(), bound), encElem(m.elem()),
                    encElem(m.key()), m.pos());
            // the inner expression reads the element the option holds, under the name given here
            case Ast.OptionRaw o -> new Ast.OptionRaw(expr(o.access(), bound),
                    rawExpr(o.inner(), bound.and(o.elemVar(), o.pos())), o.elemVar(), o.pos());
            case Ast.ObjectRaw o -> {
                List<Ast.RawEntry> entries = new ArrayList<>();
                for (Ast.RawEntry entry : o.entries()) {
                    entries.add(new Ast.RawEntry(entry.key(), rawExpr(entry.value(), bound),
                            entry.pos()));
                }
                yield new Ast.ObjectRaw(entries, o.pos());
            }
        };
    }

    private Ast.EncElem encElem(Ast.EncElem e) {
        return switch (e) {
            case Ast.PrimEnc p -> p;
            case Ast.DataEnc d -> new Ast.DataEnc(type(d.typeName()), d.pos());
            case Ast.ListElemEnc l -> new Ast.ListElemEnc(encElem(l.elem()), l.pos());
            case Ast.SetElemEnc s -> new Ast.SetElemEnc(encElem(s.elem()), s.pos());
            case Ast.MapElemEnc m -> new Ast.MapElemEnc(encElem(m.value()), encElem(m.key()), m.pos());
        };
    }

    // --- expressions ---

    private Ast.Expr expr(Ast.Expr e) {
        return expr(e, Bindings.NONE);
    }

    /**
     * Rewrites the names {@code e} itself writes, against the bindings in force where it is written.
     *
     * <p>A node that binds a name is written out here, because what its parts are resolved against
     * differs: a {@code let}'s value is outside its own binding and its body is inside. Everything
     * else recurses through {@link Ast#mapChildren}, so a new expression kind is carried without
     * being named here.
     */
    private Ast.Expr expr(Ast.Expr e, Bindings bound) {
        return switch (e) {
            case Ast.Var v -> v.denoting(answered(v.name(), v.pos(),
                    valueName(v.name(), v.pos(), bound)));
            case Ast.Call call -> new Ast.Call(call.fn(),
                    answered(call.fn(), call.pos(), calledName(call, bound)),
                    exprs(call.args(), bound), call.pos());
            case Ast.NewData nd -> {
                List<Ast.FieldInit> inits = new ArrayList<>();
                for (Ast.FieldInit i : nd.inits()) {
                    inits.add(new Ast.FieldInit(i.name(), expr(i.value(), bound), i.pos()));
                }
                // a spread names a value, so it is resolved the way a bare name is: a binding in
                // force wins over a declaration here too
                List<Ast.ValueRef> spreads = new ArrayList<>();
                for (Ast.ValueRef s : nd.spreads()) {
                    spreads.add(s.denotes() != null ? s : s.denoting(
                            answered(s.written(), s.pos(), valueName(s.written(), s.pos(), bound))));
                }
                yield new Ast.NewData(type(nd.typeName()), inits, spreads, nd.publishedBy(), nd.pos());
            }
            // a binding's pattern may write Option's `Some`, which the binding check then rejects
            // for what it is — a name that opens nothing — rather than as a name nothing declares
            case Ast.LetIn li -> new Ast.LetIn(li.name(), expr(li.value(), bound),
                    paramType(li.declaredType()), li.annotated(),
                    li.opens() == null ? null : caseName(li.opens()),
                    expr(li.body(), bound.and(li.name(), li.pos())), li.pos());
            case Ast.Block b -> new Ast.Block(b.params(),
                    expr(b.body(), bound.andAll(b.params(), b.pos())), b.pos());
            // an attempt's binder names the value only where there is one to name — the success
            // branch. The construction and the else value are outside it.
            case Ast.IfConstructed ic -> new Ast.IfConstructed(expr(ic.construct(), bound),
                    ic.binder(), expr(ic.then(), bound.and(ic.binder(), ic.pos())),
                    expr(ic.els(), bound), ic.pos());
            case Ast.Match m -> {
                List<Ast.Case> cases = new ArrayList<>();
                for (Ast.Case c : m.cases()) {
                    Bindings inArm = c.binding() == null ? bound : bound.and(c.binding(), c.pos());
                    cases.add(new Ast.Case(caseNames(c.caseTypes()), c.binding(),
                            expr(c.body(), inArm),
                            c.unwrapAsserts() == null ? null : names(c.unwrapAsserts()), c.pos()));
                }
                yield new Ast.Match(expr(m.scrutinee(), bound), cases, m.pos());
            }
            default -> Ast.mapChildren(e, x -> expr(x, bound));
        };
    }

    private List<Ast.Expr> exprs(List<Ast.Expr> es) {
        return exprs(es, Bindings.NONE);
    }

    private List<Ast.Expr> exprs(List<Ast.Expr> es, Bindings bound) {
        List<Ast.Expr> out = new ArrayList<>();
        for (Ast.Expr e : es) {
            out.add(expr(e, bound));
        }
        return out;
    }

    // --- names in a body ---

    /**
     * What a name used as a value denotes. A binding in force wins over everything else — a body may
     * bind a name a module declares, and the binding is what the name means there.
     */
    private ValueName valueName(String written, SourcePos pos, Bindings bound) {
        SourcePos binder = bound.binderOf(written);
        if (binder != null) {
            return new ValueName.Local(written, binder);
        }
        if (Elaborator.ROUNDING_MODES.contains(written) || written.equals("None")
                || written.equals("Some")) {
            return new ValueName.Builtin(written);
        }
        TypeName type = symbols.resolve(written);
        if (type != null && !type.isUnresolved()) {
            return new ValueName.OfType(written, type, null);
        }
        // a helper or a behavior named without being applied — handed to a combinator by name,
        // which the inliner expands into a block that applies it
        ValueName.Helper helper = values.helpers().get(written);
        if (helper != null) {
            return helper;
        }
        ValueName.Behavior behavior = values.behaviors().get(written);
        if (behavior != null) {
            return behavior;
        }
        return nothing(written, pos, unknownIdentifier(written, pos, bound));
    }

    /** What the name a call applies denotes. */
    private ValueName calledName(Ast.Call call, Bindings bound) {
        String written = call.fn();
        SourcePos binder = bound.binderOf(written);
        if (binder != null) {
            return new ValueName.Local(written, binder);   // a function-typed parameter, applied
        }
        if (written.equals("Some") || written.equals("None")) {
            return new ValueName.Builtin(written);   // Option's cases, which are not calls (E1303)
        }
        // A library qualifier makes this a library reference — `Date(...)`, whose namespace is the
        // whole name, included. Whether the library has a function of that name is the check's to
        // say: asking here would tie the answer to how much of the library has been loaded, and the
        // library resolves its own sources while it loads.
        int dot = written.lastIndexOf('.');
        if (Prelude.isQualifier(dot < 0 ? written : written.substring(0, dot))) {
            return new ValueName.Stdlib(written);
        }
        ValueName.Helper helper = values.helpers().get(written);
        if (helper != null) {
            return helper;
        }
        ValueName.Behavior behavior = values.behaviors().get(written);
        if (behavior != null) {
            return behavior;
        }
        TypeName type = symbols.resolve(written);
        if (type != null && !type.isUnresolved()) {
            return new ValueName.OfType(written, type, null);   // a newtype applied to what it wraps
        }
        return nothing(written, call.pos(), notCallable(written, call.pos(), bound));
    }

    /**
     * Records what a name used as a value was answered with, and hands it back.
     *
     * <p>A name that denotes a type — a unit data written as a value, a newtype applied to what it
     * wraps — is a use of that type as much as one written in a field's type is, and is recorded as
     * one too. Otherwise renaming the type would rewrite every other mention of it and leave these,
     * which is a rename that stops the workspace compiling.
     */
    private ValueName answered(String written, SourcePos pos, ValueName denotes) {
        if (pos == null) {
            return denotes;
        }
        values0.add(new ValueUse(written, denotes, pos));
        if (denotes instanceof ValueName.OfType named) {
            denotations.add(new Denotation(written, named.type(), pos));
        }
        return denotes;
    }

    /** Records that a name in a body denotes nothing, and gives it the name that says so. */
    private ValueName nothing(String written, SourcePos pos, CompileException why) {
        unresolved.add(why);
        return new ValueName.Unresolved(written);
    }

    /** The names a body could have written where it wrote one nothing answers to. */
    private List<String> reachable(Bindings bound) {
        List<String> names = new ArrayList<>(bound.byName().keySet());
        names.addAll(values.helpers().keySet());
        names.addAll(values.behaviors().keySet());
        return names;
    }

    private CompileException unknownIdentifier(String written, SourcePos pos, Bindings bound) {
        if (written.equals("null")) {
            return new CompileException(pos, "E1301",
                    "`null` is not part of the language. Use an optional field with `?`.");
        }
        List<String> candidates = reachable(bound);
        return CompileException.of(
                Diagnostic.of(null, "check.unknown.name.msg").title("check.unknown.title")
                        .at(pos, written.length()).args(written)
                        .suggestion(Suggest.candidate(written, candidates)).build(),
                "unknown identifier `" + written + "`" + Suggest.hint(written, candidates));
    }

    /**
     * A name applied to arguments that names nothing that can be applied. A standard-library
     * function written bare is told apart: it exists, and is reached qualified (spec §stdlib).
     */
    private CompileException notCallable(String written, SourcePos pos, Bindings bound) {
        String qualified = Prelude.qualifiedFor(written);
        if (qualified != null) {
            return CompileException.of(
                    Diagnostic.of(null, "check.stdlib.qualified.msg").title("check.unknown.title")
                            .at(pos, written.length()).args(written, qualified).build(),
                    "`" + written + "` is a standard-library function and must be called qualified,"
                            + " as `" + qualified + "` (spec §stdlib).");
        }
        List<String> candidates = reachable(bound);
        return CompileException.of(
                Diagnostic.of("E1401", "e1401.msg").at(pos, written.length()).args(written)
                        .suggestion(Suggest.candidate(written, candidates))
                        .hint("e1401.hint").build(),
                "`" + written + "` is not a behavior or builtin" + Suggest.hint(written, candidates)
                        + ". Calling arbitrary JVM methods is not allowed; declare a behavior"
                        + " without a `let` and implement it from Java.");
    }

    /**
     * The names bound at a point in a body, each with where it was bound. Persistent: extending it
     * leaves the outer scope as it was, which is what an inner binding shadowing an outer one is.
     */
    record Bindings(Map<String, SourcePos> byName) {

        static final Bindings NONE = new Bindings(Map.of());

        Bindings and(String name, SourcePos binder) {
            Map<String, SourcePos> next = new HashMap<>(byName);
            next.put(name, binder);
            return new Bindings(Map.copyOf(next));
        }

        Bindings andAll(List<String> names, SourcePos binder) {
            Map<String, SourcePos> next = new HashMap<>(byName);
            for (String name : names) {
                next.put(name, binder);
            }
            return new Bindings(Map.copyOf(next));
        }

        SourcePos binderOf(String name) {
            return byName.get(name);
        }
    }

    // --- names ---

    private List<Ast.Name> names(List<Ast.Name> names) {
        List<Ast.Name> out = new ArrayList<>();
        for (Ast.Name n : names) {
            out.add(type(n));
        }
        return out;
    }

    /** A name that must denote a declared type. */
    private Ast.Name type(Ast.Name n) {
        if (n.denotes() != null) {
            return n;
        }
        TypeName denoted = symbols.resolve(n.written());
        if (denoted == null) {
            return answered(n.denoting(nothingDenotes(n)));
        }
        return answered(n.denoting(denoted));
    }

    /** The names a {@code match} arm may write: a declared case, a primitive heading a union
     * ({@code Int} in {@code Int | DivisionByZero}), a runtime error case, or one of Option's two.
     * A declared type wins over Option's names, so a model may still declare {@code Some}. */
    private List<Ast.Name> caseNames(List<Ast.Name> names) {
        List<Ast.Name> out = new ArrayList<>();
        for (Ast.Name n : names) {
            out.add(caseName(n));
        }
        return out;
    }

    private Ast.Name caseName(Ast.Name n) {
        if (n.denotes() != null) {
            return n;
        }
        TypeName denoted = symbols.resolveCase(n.written());
        if (denoted == null) {
            denoted = TypeName.optionCase(n.written());
        }
        if (denoted == null) {
            return answered(n.denoting(nothingDenotes(n)));
        }
        return answered(n.denoting(denoted));
    }

    /**
     * What a reference denotes, or {@link souther.compiler.types.Type#ERRONEOUS} when nothing does.
     *
     * <p>This pass is where a failure becomes a value. {@link TypeOps#denoted} answers or says it
     * cannot, because it is asked one reference at a time and has nowhere to put a report; here there
     * is somewhere to put it, and a tree to carry on resolving.
     */
    private Type typeOf(Ast.TypeRef ref) {
        try {
            return TypeOps.denoted(ref, symbols);
        } catch (CompileException e) {
            unresolved.add(e);
            return Type.ERRONEOUS;
        }
    }

    /** Records that {@code n} denotes nothing, and gives it the name that says so. */
    private TypeName nothingDenotes(Ast.Name n) {
        unresolved.add(TypeOps.unknownType(n.written(), n.pos(), symbols));
        return TypeName.unresolved(n.written());
    }

    /** Records what a name was answered with, and hands it back. A name with no position was
     * synthesized by an earlier pass rather than written, so there is nothing to point at. */
    private Ast.Name answered(Ast.Name n) {
        if (n.pos() != null) {
            denotations.add(new Denotation(n.written(), n.denotes(), n.pos()));
        }
        return n;
    }
}
