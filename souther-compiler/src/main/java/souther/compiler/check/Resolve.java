package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.ast.WrittenName;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticCode;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructionOrigin;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.types.ValueName;
import souther.compiler.Prelude;
import souther.compiler.Reserved;

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
    /** What each binding this pass gave an identity to is called, and where that is written. */
    private final Map<BindingId, BoundName> binders = new LinkedHashMap<>();
    /** How many bindings each definition has been given, so the next one gets the next number. */
    private final Map<BindingOwner, Integer> counts = new HashMap<>();
    /** The definition whose text is being read. Every binding met belongs to it. */
    private BindingOwner owner;

    private Resolve(Symbols symbols, Values values) {
        this.symbols = symbols;
        this.values = values;
    }

    /** The value definition of this spelling in this module. */
    private BindingOwner ownerOfValue(String name) {
        return new BindingOwner.OfValue(values.module(), name);
    }

    /** A binder answered, and the bindings that hold under it. */
    private record Answered(Ast.Binder binder, Bindings bound) {}

    /**
     * {@code binder} given a binding of its own, and {@code bound} extended with it.
     *
     * <p>The binding is what the names under it are answered with, so two bindings of one spelling
     * are two answers however they were written. Where it was written is kept aside, for a reader
     * that is asking about the source rather than about the program.
     */
    private Answered bind(Bindings bound, Ast.Binder binder) {
        int ordinal = counts.merge(owner, 1, Integer::sum) - 1;
        BindingId id = new BindingId(owner, ordinal);
        if (binder.namePos() != null) {
            // Only a name the author wrote is a place a reader can be sent to or asked about. A
            // desugaring's binding is anchored on the form it came from, which is a place holding
            // something the author did write.
            binders.put(id, new BoundName(binder.written()));
        }
        return new Answered(
                new Ast.Binder.Bound(binder.written(), id, binder.pos()),
                bound.and(binder.name(), new ValueName.Local(binder.name(), id)));
    }

    /** The bindings under {@code binder}, where the binder itself is not carried on. */
    private Bindings binding(Bindings bound, Ast.Binder binder) {
        return bind(bound, binder).bound();
    }

    /** Several binders answered, and the bindings that hold under all of them. */
    private record AnsweredAll(List<Ast.Binder> binders, Bindings bound) {}

    /** The same as {@link #bind}, for the names one binder writes at once — a block's parameters. */
    private AnsweredAll bindAll(Bindings bound, List<Ast.Binder> written) {
        List<Ast.Binder> out = new ArrayList<>();
        for (Ast.Binder b : written) {
            Answered a = bind(bound, b);
            bound = a.bound();
            out.add(a.binder());
        }
        return new AnsweredAll(out, bound);
    }

    /**
     * What a module can name in the value namespace without a binding: its own helpers, and the
     * behaviors it can reach.
     *
     * <p>The behaviors come from outside — an import brings one in — so they are given rather than
     * read off the module. A module resolved on its own reaches only what it declares.
     */
    public record Values(String module, Map<String, ValueName.Helper> helpers,
                         Map<String, ValueName.Behavior> behaviors,
                         Map<String, String> exposed) {

        /**
         * What a module reaches when nothing else is in sight — the core modules, which the library
         * resolves as it loads. A core module imports nothing (it declares the library), so the
         * table of names an import would bring in is empty; a module that does import is resolved
         * with what the query answered, which reads its imports from the source that wrote them.
         */
        public static Values of(Ast.Module m) {
            Map<String, ValueName.Helper> helpers = new LinkedHashMap<>();
            for (String helper : HelperInliner.helpersOf(m).keySet()) {
                helpers.put(helper, new ValueName.Helper(m.name(), helper));
            }
            Map<String, ValueName.Behavior> behaviors = new LinkedHashMap<>();
            for (Ast.BehaviorDef b : m.behaviors()) {
                behaviors.put(b.name(), new ValueName.Behavior(m.name(), b.name()));
            }
            return new Values(m.name(), helpers, behaviors, Map.of());
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
     * @param written the occurrence the name was read from — the name, the characters that spell
     *                it there, and where they are
     * @param denotes what it names
     */
    public record Denotation(WrittenName written, TypeName denotes) {

        /** Where the name is written. */
        public SourcePos pos() {
            return written.pos();
        }
    }

    /**
     * One written name in the value namespace and what it turned out to denote, where it was
     * written. What {@link Denotation} is for a type, and collected for the same reason: an editor
     * asking what is under the cursor is asking about the answer this traversal already gave.
     */
    public record ValueUse(WrittenName written, ValueName denotes) {

        /** Where the name is written. */
        public SourcePos pos() {
            return written.pos();
        }
    }

    /**
     * A resolved module, every name the pass answered in it, and the names it could not answer.
     *
     * <p>A name that denotes nothing does not end the pass. It denotes {@link TypeName#unresolved},
     * which becomes {@link souther.compiler.types.Type#ERRONEOUS}, and the rest of the module is
     * resolved as if the mistake were not there — so an author is told about every unknown name at
     * once instead of one per compile, and an editor can still say what the names around it mean.
     *
     * <p>{@code binders} says what each binding is called and where the author wrote that name. A
     * binding is not its position — a pass that expands a helper stamps the call site over the
     * positions in the copy — so the two are kept apart, and a reader asking about the source rather
     * than about the program reads this. The characters that spell it come with it, because a reader
     * asking what a cursor is on has to know how far the name reaches, and neither a position nor
     * the name alone says.
     *
     * <p>Only the bindings whose names the author wrote are in it. A desugaring binds a value to a
     * name of its own — the parameter {@code .field} becomes, the value a {@code match} is held in —
     * and anchors it on the form it was rewriting. That anchor is a place in the source holding
     * something else, so a reader answered with one of these would be answered about a name that is
     * not there, at a width that is not its.
     */
    public record Resolved(Ast.Module module, List<Denotation> denotations, List<ValueUse> values,
                           List<CompileException> unresolved, Map<BindingId, BoundName> binders) {}

    /** What a binding is called, and the occurrence of that name the author wrote. */
    public record BoundName(WrittenName written) {

        /** Where the name is written. */
        public SourcePos pos() {
            return written.pos();
        }
    }

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
                case Ast.SpecBehavior spec -> new Ast.SpecBehavior(spec.written(), r.params(spec.params()),
                        r.retType(spec.ret()), r.names(spec.constructs()), spec.dependsOn(), spec.pos());
                case Ast.PipeBehavior pipe -> new Ast.PipeBehavior(pipe.written(), pipe.stages(),
                        r.retType(pipe.declaredOut()), pipe.pos());
            });
        }
        List<Ast.FnDef> fns = new ArrayList<>();
        for (Ast.FnDef fn : m.fns()) {
            fns.add(r.fn(fn));
        }
        List<Ast.Example> examples = new ArrayList<>();
        for (Ast.Example e : m.examples()) {
            r.owner = r.ownerOfValue(e.target());
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
            r.owner = r.ownerOfValue(f.target());
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
                List.copyOf(r.denotations), List.copyOf(r.values0), List.copyOf(r.unresolved),
                Map.copyOf(r.binders));
    }

    private Ast.FnDef fn(Ast.FnDef f) {
        owner = ownerOfValue(f.name());
        List<Ast.FnParam> params = new ArrayList<>();
        Bindings bound = Bindings.NONE;
        for (Ast.FnParam p : f.params()) {
            Answered a = bind(bound, p.binder());
            params.add(new Ast.FnParam(a.binder(), paramType(p.type()), p.typeFromPattern()));
            bound = a.bound();
        }
        Ast.FnBody body = switch (f.body()) {
            case Ast.FnBody.Written w -> new Ast.FnBody.Written(expr(w.expr(), bound));
            case Ast.FnBody.Intrinsic i -> i;
        };
        return new Ast.FnDef(f.written(), f.declaredIn(), params, retType(f.declaredReturn()), body,
                f.modifiers(), f.pos());
    }

    // --- written types ---

    private List<Ast.Param> params(List<Ast.Param> params) {
        List<Ast.Param> out = new ArrayList<>();
        for (Ast.Param p : params) {
            out.add(new Ast.Param(p.written(), retType(p.type())));
        }
        return out;
    }

    private List<Ast.Field> fields(List<Ast.Field> fields) {
        List<Ast.Field> out = new ArrayList<>();
        for (Ast.Field f : fields) {
            out.add(new Ast.Field(f.written(), typeTerm(f.type())));
        }
        return out;
    }

    private Ast.RetType paramType(Ast.RetType t) {
        return retType(t);
    }

    private Ast.RetType retType(Ast.RetType ret) {
        if (ret == null) {
            return null;
        }
        List<Ast.TypeTerm> cases = new ArrayList<>();
        for (Ast.TypeTerm c : ret.cases()) {
            cases.add(typeTerm(c));
        }
        return new Ast.RetType(cases, ret.pos());
    }

    private Ast.TypeTerm typeTerm(Ast.TypeTerm t) {
        return switch (t) {
            case null -> null;
            case Ast.TypeRef ref -> typeRef(ref);
            case Ast.FnType ft -> {
                List<Ast.RetType> ps = new ArrayList<>();
                for (Ast.RetType p : ft.params()) {
                    ps.add(retType(p));
                }
                yield new Ast.FnType(ps, retType(ft.result()), ft.pos());
            }
        };
    }

    /** A written type reference, with what it denotes decided here — once, and in the module that
     * wrote it, so no later reader has to know where it was written. */
    private Ast.TypeRef typeRef(Ast.TypeRef ref) {
        if (ref == null || ref.denotes() != null) {
            return ref;
        }
        Ast.TypeTerm arg = typeTerm(ref.arg());
        List<Ast.TypeTerm> elems = null;
        if (ref.tupleElems() != null) {
            elems = new ArrayList<>();
            for (Ast.TypeTerm e : ref.tupleElems()) {
                elems.add(typeTerm(e));
            }
        }
        Ast.TypeRef resolved = new Ast.TypeRef(ref.written(), arg, elems, null, ref.anchor());
        Ast.TypeRef denoted = resolved.denoting(typeOf(resolved));
        // A reference with no name is a tuple or a container shape, which names no declaration.
        if (denoted.name() != null && denoted.pos() != null) {
            TypeName names = symbols.resolve(denoted.name());
            if (names != null) {
                denotations.add(new Denotation(denoted.written(), names));
            }
        }
        return denoted;
    }

    // --- definitions ---

    private Ast.Def def(Ast.Def def) {
        owner = new BindingOwner.OfData(symbols.own(def.name()));
        return switch (def) {
            case Ast.UnitData u -> u;
            // an invariant reads the fields of the data it belongs to, which are what bind its
            // names — `value > 0` is about this declaration's `value`, whatever else is in scope
            case Ast.Data d -> {
                declareFields(d);
                yield new Ast.Data(d.written(), d.newtype(), names(d.includes()), fields(d.fields()),
                        Ast.mapClauses(d.invariants(), inv -> expr(inv, boundFields(d))),
                        d.decoder().map(this::decoder), d.encoder().map(this::encoder),
                        d.pos());
            }
            case Ast.SumData s -> new Ast.SumData(s.written(), sumCases(s), s.decoder().map(this::discriminate),
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
                        Diagnostic.of(DiagnosticCode.E1020, "check.sum.unknowncase")
                                .at(s.pos()).args(c.written(), s.name()).build(),
                        "unknown case `" + c.written() + "` in sum `" + s.name() + "`");
            }
            // Recorded like any other written name. A case is a name this module wrote and this pass
            // answered, so leaving it out made it a use nothing could see — an editor asked about it
            // had no answer, and a reader asking which imports are written found the name missing.
            out.add(answered(c.denoting(denoted)));
        }
        return out;
    }

    /**
     * The fields of a declaration, as the names its own invariant reads — the ones written here and
     * the ones a spread brings in, which are as much this declaration's fields as the written ones
     * (and are what a spread-in invariant was written against).
     */
    /**
     * Where each field this declaration writes is written, against the binding it introduces inside
     * an invariant.
     *
     * <p>Recorded whether or not this declaration has an invariant of its own: a declaration that
     * includes it reads these fields in <em>its</em> invariant, and the binding a field is stays the
     * declaring declaration's, so this is where an editor is answered from either way.
     */
    private void declareFields(Ast.Data d) {
        Map<String, BindingId> bindings = TypeOps.fieldBindings(d, symbols);
        for (Ast.Field field : d.fields()) {
            BindingId binding = bindings.get(field.name());
            if (binding != null) {
                binders.put(binding, new BoundName(field.written()));   // OfFields
            }
        }
    }

    private Bindings boundFields(Ast.Data d) {
        Bindings bound = Bindings.NONE;
        // which binding each field is is answered in one place, so the pass that emits this
        // invariant reaches the same ones without working them out again
        for (Map.Entry<String, BindingId> f : TypeOps.fieldBindings(d, symbols).entrySet()) {
            bound = bound.and(f.getKey(), new ValueName.Local(f.getKey(), f.getValue()));
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
                Answered input = bind(Bindings.NONE, p.input());
                Bindings bound = input.bound();
                List<Ast.DecStmt> stmts = new ArrayList<>();
                for (Ast.DecStmt s : p.stmts()) {
                    if (s instanceof Ast.Let let) {
                        Ast.Expr value = expr(let.value(), bound);
                        Answered a = bind(bound, let.binder());
                        stmts.add(new Ast.Let(a.binder(), value, let.pos()));
                        bound = a.bound();
                    } else {
                        stmts.add(s);
                    }
                }
                yield new Ast.PrimDecoder(p.from(), input.binder(), stmts,
                        construct(p.result(), bound), p.pos());
            }
            case Ast.ObjectDecoder o -> {
                List<Ast.Bind> binds = new ArrayList<>();
                Bindings bound = Bindings.NONE;
                for (Ast.Bind b : o.binds()) {
                    Answered a = bind(bound, b.binder());
                    binds.add(new Ast.Bind(a.binder(), b.key(), decRef(b.ref()), b.pos()));
                    bound = a.bound();
                }
                yield new Ast.ObjectDecoder(binds, construct(o.result(), bound), o.pos());
            }
            case Ast.NewtypeDecoder n -> {
                Answered input = bind(Bindings.NONE, n.input());
                yield new Ast.NewtypeDecoder(decRef(n.inner()), input.binder(),
                        construct(n.result(), input.bound()), n.pos());
            }
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
            inits.add(new Ast.FieldInit(i.written(), expr(i.value(), bound)));
        }
        return new Ast.Construct(type(c.typeName()), inits, c.pos());
    }

    // --- encoders ---

    /** An encoder reads the value it is encoding under the name it gives it. */
    private Ast.EncoderDef encoder(Ast.EncoderDef e) {
        Answered self = bind(Bindings.NONE, e.self());
        return new Ast.EncoderDef(self.binder(), rawExpr(e.result(), self.bound()), e.pos());
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
            case Ast.OptionRaw o -> {
                Answered elem = bind(bound, o.elem());
                yield new Ast.OptionRaw(expr(o.access(), bound),
                        rawExpr(o.inner(), elem.bound()), elem.binder(), o.pos());
            }
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
            case Ast.Var v -> v.denoting(answered(v.written(), valueName(v.written(), bound)));
            // Applying a name is answered as a name: which of a binding, a helper, a library
            // function or a type it is decides what the application means. Applying anything else
            // is answered as the expression it is, and what may be applied is the check's to say.
            case Ast.Apply call when call.appliesAName() -> new Ast.Apply(call.written(),
                    answered(call.name(), calledName(call, bound)),
                    exprs(call.args(), bound), call.origin(), call.pos());
            case Ast.Apply call -> new Ast.Apply(callee(call.function(), bound),
                    exprs(call.args(), bound), call.origin(), call.pos());
            // `Map.empty`, `String.isEmpty`, `up.Amount` — a namespace and a member of it, which
            // the parser read as a field taken off a name because it reads no case at all. Folded
            // here and nowhere earlier: `Map` may be a parameter, and a binding in force wins over
            // everything else — which is a fact the parser and the AST builder do not have.
            case Ast.FieldAccess fa -> {
                Ast.Var member = qualifiedName(fa, false, bound);
                yield member != null ? member
                        : new Ast.FieldAccess(expr(fa.target(), bound), fa.field(), fa.pos());
            }
            // the type being built is this case's business; everything under it is a slot like any
            // other
            case Ast.NewData nd -> Ast.mapChildren(
                    new Ast.NewData(type(nd.typeName()), nd.inits(), nd.spreads(), nd.origin(), nd.pos()),
                    x -> expr(x, bound), s -> name(s, bound));
            // a binding's pattern may write Option's `Some`, which the binding check then rejects
            // for what it is — a name that opens nothing — rather than as a name nothing declares
            case Ast.LetIn li -> {
                Ast.Expr value = expr(li.value(), bound);
                Answered a = bind(bound, li.binder());
                yield new Ast.LetIn(a.binder(), value,
                        paramType(li.declaredType()), li.annotated(),
                        li.opens() == null ? null : caseName(li.opens()),
                        expr(li.body(), a.bound()), li.pos());
            }
            case Ast.Block b -> {
                AnsweredAll ps = bindAll(bound, b.params());
                yield new Ast.Block(ps.binders(), expr(b.body(), ps.bound()), b.pos());
            }
            // an attempt's binder names the value only where there is one to name — the success
            // branch. The construction and the else value are outside it.
            case Ast.IfConstructed ic -> {
                Answered a = bind(bound, ic.binder());
                yield new Ast.IfConstructed(expr(ic.construct(), bound), a.binder(),
                        expr(ic.then(), a.bound()), arms(ic.els(), bound), ic.pos());
            }
            case Ast.Match m -> {
                List<Ast.Case> cases = new ArrayList<>();
                for (Ast.Case c : m.cases()) {
                    Answered a = c.binding() == null ? null : bind(bound, c.binding());
                    Bindings inArm = a == null ? bound : a.bound();
                    cases.add(new Ast.Case(caseNames(c.caseTypes()),
                            a == null ? null : a.binder(), expr(c.body(), inArm),
                            c.unwrapAsserts() == null ? null : names(c.unwrapAsserts()), c.pos()));
                }
                yield new Ast.Match(expr(m.scrutinee(), bound), cases, m.pos());
            }
            default -> Ast.mapChildren(e, x -> expr(x, bound), s -> name(s, bound));
        };
    }

    /**
     * One name in the value namespace, answered against the bindings in force where it is written —
     * what this pass does at a name slot, wherever a node has one. A binding in force wins over a
     * declaration in a spread as everywhere else.
     *
     * <p>A name a pass synthesized already knowing what it means is left as it is, as a synthesized
     * type name is.
     */
    private Ast.Var name(Ast.Var written, Bindings bound) {
        return written.denotes() != null ? written
                : written.denoting(answered(written.written(), valueName(written.written(), bound)));
    }

    private List<Ast.ElseArm> arms(List<Ast.ElseArm> arms, Bindings bound) {
        List<Ast.ElseArm> out = new ArrayList<>();
        for (Ast.ElseArm arm : arms) {
            out.add(arm.with(expr(arm.body(), bound)));
        }
        return out;
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
     * What a name written in the value namespace denotes, or null where nothing here does.
     *
     * <p>One ladder, in one order, so a name means the same thing under an application as beside one.
     * It was two — a bare name tried the declared types before this module's helpers, an applied one
     * tried the library first and the types last — and which rung answered therefore depended on
     * whether a `(` followed. The rungs a spelling could reach twice are refused where the value
     * namespace is assembled, so the order between them decides nothing.
     *
     * <p>{@code applied} is the one thing the position still says. A type written as a value is the
     * construction of a unit data and records where it came from; applied, it is a newtype taking
     * what it wraps, and the application is what says that.
     */
    private ValueName lookup(String written, boolean applied, Bindings bound) {
        // a binding in force wins over everything else: a body may bind a name a module declares,
        // and the binding is what the name means there
        ValueName.Local binding = bound.binderOf(written);
        if (binding != null) {
            return binding;
        }
        // names the language itself gives: Option's two cases
        if (written.equals("None") || written.equals("Some")) {
            return new ValueName.Builtin(written);
        }
        // A library qualifier makes this a library reference — `Date(...)`, whose namespace is the
        // whole name, included. Whether the library has a member of that name is the check's to say:
        // asking here would tie the answer to how much of the library has been loaded, and the
        // library resolves its own sources while it loads.
        //
        // A `private` declaration is the exception, and asking about it here is safe for the same
        // reason: the only modules that may name one are the library's own, and they are told yes
        // without the entry being looked up at all.
        int dot = written.lastIndexOf('.');
        if (Prelude.isQualifier(dot < 0 ? written : written.substring(0, dot))) {
            if (Reserved.isNamespace(values.module()) || !Prelude.isPrivateMember(written)) {
                return new ValueName.Stdlib(written);
            }
            return null;
        }
        TypeName type = symbols.resolve(written);
        if (type != null && !type.isUnresolved()) {
            return new ValueName.OfType(written, type, applied ? null : ConstructionOrigin.own());
        }
        // a helper or a behavior, applied or handed over by name — which the inliner expands into a
        // block that applies it
        ValueName.Helper helper = values.helpers().get(written);
        if (helper != null) {
            return helper;
        }
        ValueName.Behavior behavior = values.behaviors().get(written);
        if (behavior != null) {
            return behavior;
        }
        // A name an import let this module write without its qualifier. Asked last: an import brings
        // a name in, and everything the module already has — a binding in force, its own
        // declarations — is what that name means here instead.
        String qualified = values.exposed().get(written);
        return qualified == null ? null : new ValueName.Stdlib(qualified);
    }

    /**
     * The callee of an application that does not apply a bare name.
     *
     * <p>A field read in this position may be a qualified name — {@code Map.empty(k)},
     * {@code up.Amount(n)} — and it is answered here rather than as a value, because applied is
     * what the position says: a type written as a value is a unit data's construction, and applied
     * it is a newtype taking what it wraps. Anything else is the expression it is, and what may be
     * applied is the check's to say.
     */
    private Ast.Expr callee(Ast.Expr function, Bindings bound) {
        if (function instanceof Ast.FieldAccess fa) {
            Ast.Var name = qualifiedName(fa, true, bound);
            if (name != null) {
                return name;
            }
        }
        return expr(function, bound);
    }

    /**
     * A chain of names read as one qualified name — {@code Map.empty}, {@code up.Amount},
     * {@code probe.a.Amount}, where the module's own name is dotted — or null where it is an
     * ordinary field read.
     *
     * <p>Only where the chain's root is unbound. A parameter or a {@code let} named {@code Map}
     * makes {@code Map.empty} that binding's {@code empty} field, resolved the ordinary way, and no
     * qualified name is produced.
     *
     * <p>The whole chain is asked first, and a chain that answers nothing is left for the caller to
     * take apart — so {@code probe.a.defaultAmount.value} folds {@code probe.a.defaultAmount} and
     * reads {@code .value} off it. What is reported, and where, is
     * {@link #unknownMember}'s to say: a member of a namespace that has no such member is named in
     * full, and a chain rooted at a name nothing declares is reported at that name.
     *
     * <p>Positioned at the root, so what a reader asks about covers every token of the name.
     */
    private Ast.Var qualifiedName(Ast.FieldAccess fa, boolean applied, Bindings bound) {
        Ast.Var root = rootName(fa);
        if (root == null || root.denotes() != null || bound.binderOf(root.name()) != null) {
            return null;
        }
        WrittenName written = dottedName(fa);
        ValueName denotes = lookup(written.canonical(), applied, bound);
        if (denotes != null) {
            return new Ast.Var(written, answered(written, denotes));
        }
        return unknownMember(fa, written, applied, bound);
    }

    /**
     * The report for a chain whose spelling denotes nothing, or null where there is nothing to say
     * here and the chain is taken apart instead.
     *
     * <p>Something is said only where the part in front is a namespace: {@code probe.a.NoSuch}
     * names a module that exists and a member it has not got, and reporting the root {@code probe}
     * as an unknown identifier would send the author after a module name that is right. Where the
     * front is not a namespace — {@code unknown.member} — nothing is said, and the root is reported
     * as the unknown identifier it is once the chain is read as the field access it turned out to
     * be.
     */
    private Ast.Var unknownMember(Ast.FieldAccess fa, WrittenName written, boolean applied,
                                  Bindings bound) {
        WrittenName qualifier = dottedName(fa.target());
        if (qualifier == null || !isNamespace(qualifier.canonical())) {
            return null;
        }
        CompileException why = applied ? notCallable(written, bound)
                : unknownIdentifier(written, bound);
        return new Ast.Var(written, answered(written, nothing(written.canonical(), why)));
    }

    /** Whether {@code qualifier} names a namespace a member may be reached through: a
     *  standard-library one, or a module of this compilation (or an alias for one). */
    private boolean isNamespace(String qualifier) {
        return Prelude.isQualifier(qualifier) || symbols.moduleOfQualifier(qualifier) != null;
    }

    /** The name a chain of field reads is rooted at, or null where it is rooted at anything else —
     *  a call's result, a parenthesised expression — which no qualified name can be. */
    private static Ast.Var rootName(Ast.Expr e) {
        return switch (e) {
            case Ast.Var v -> v;
            case Ast.FieldAccess fa -> rootName(fa.target());
            default -> null;
        };
    }

    /** The dotted spelling of a chain of names, or null where it is not one. */
    private static WrittenName dottedName(Ast.Expr e) {
        return switch (e) {
            case Ast.Var v -> v.written();
            case Ast.FieldAccess fa -> {
                WrittenName target = dottedName(fa.target());
                yield target == null ? null : target.then(fa.name());
            }
            default -> null;
        };
    }

    /** What a name used as a value denotes, and the report for one that denotes nothing. */
    private ValueName valueName(WrittenName written, Bindings bound) {
        ValueName denotes = lookup(written.canonical(), false, bound);
        return denotes != null ? denotes
                : nothing(written.canonical(), unknownIdentifier(written, bound));
    }

    /** The same, for the name an application applies: what is not there is reported differently. */
    private ValueName calledName(Ast.Apply call, Bindings bound) {
        ValueName denotes = lookup(call.written(), true, bound);
        return denotes != null ? denotes
                : nothing(call.written(), notCallable(call.name(), bound));
    }

    /**
     * Records what a name used as a value was answered with, and hands it back.
     *
     * <p>A name that denotes a type — a unit data written as a value, a newtype applied to what it
     * wraps — is a use of that type as much as one written in a field's type is, and is recorded as
     * one too. Otherwise renaming the type would rewrite every other mention of it and leave these,
     * which is a rename that stops the workspace compiling.
     */
    private ValueName answered(WrittenName written, ValueName denotes) {
        if (written.pos() == null) {
            return denotes;
        }
        values0.add(new ValueUse(written, denotes));
        if (denotes instanceof ValueName.OfType named) {
            denotations.add(new Denotation(written, named.type()));
        }
        return denotes;
    }

    /** Records that a name in a body denotes nothing, and gives it the name that says so. */
    private ValueName nothing(String written, CompileException why) {
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

    /**
     * The report for a spelling under a library qualifier that the library has no member for, or
     * null where the spelling is not one. A {@code private} declaration lands here: from outside the
     * reserved namespace the library has no such member, which is what a caller is told — the same
     * answer a misspelling gets, because from where the caller stands they are the same thing.
     */
    private CompileException notALibraryMember(WrittenName written) {
        String name = written.canonical();
        int dot = name.lastIndexOf('.');
        if (dot < 0 || !Prelude.isQualifier(name.substring(0, dot))) {
            return null;
        }
        return CompileException.of(
                Diagnostic.uncoded("check.stdlib.notfunction").title("check.unknown.title")
                        .at(written.region()).args(written.quoted()).build(),
                "`" + written.quoted() + "` is not a standard-library function.");
    }

    private CompileException unknownIdentifier(WrittenName written, Bindings bound) {
        String name = written.canonical();
        if (name.equals("null")) {
            return CompileException.of(
                    Diagnostic.of(DiagnosticCode.E1301, "e1301.msg").at(written.region()).build(),
                    "`null` is not part of the language. Use an optional field with `?`.");
        }
        CompileException notALibraryMember = notALibraryMember(written);
        if (notALibraryMember != null) {
            return notALibraryMember;
        }
        List<String> candidates = reachable(bound);
        return CompileException.of(
                Diagnostic.uncoded("check.unknown.name.msg").title("check.unknown.title")
                        .at(written.region()).args(written.quoted())
                        .suggestion(Suggest.candidate(name, candidates)).build(),
                "unknown identifier `" + written.quoted() + "`" + Suggest.hint(name, candidates));
    }

    /**
     * A name applied to arguments that names nothing that can be applied. A standard-library
     * function written bare is told apart: it exists, and is reached qualified (spec §stdlib).
     */
    private CompileException notCallable(WrittenName written, Bindings bound) {
        CompileException notALibraryMember = notALibraryMember(written);
        if (notALibraryMember != null) {
            return notALibraryMember;
        }
        String name = written.canonical();
        String qualified = Prelude.qualifiedFor(name);
        if (qualified != null) {
            return CompileException.of(
                    Diagnostic.uncoded("check.stdlib.qualified.msg").title("check.unknown.title")
                            .at(written.region()).args(written.quoted(), qualified)
                            .build(),
                    "`" + written.quoted() + "` is a standard-library function and must be called"
                            + " qualified, as `" + qualified + "` (spec §stdlib).");
        }
        List<String> candidates = reachable(bound);
        return CompileException.of(
                Diagnostic.of(DiagnosticCode.E1401, "e1401.msg").at(written.region())
                        .args(written.quoted())
                        .suggestion(Suggest.candidate(name, candidates))
                        .hint("e1401.hint").build(),
                "`" + written.quoted() + "` is not a behavior or builtin"
                        + Suggest.hint(name, candidates)
                        + ". Calling arbitrary JVM methods is not allowed; declare a behavior"
                        + " without a `let` and implement it from Java.");
    }

    /**
     * The names bound at a point in a body, each with the binding it is. Persistent: extending it
     * leaves the outer scope as it was, which is what an inner binding shadowing an outer one is.
     */
    record Bindings(Map<String, ValueName.Local> byName) {

        static final Bindings NONE = new Bindings(Map.of());

        Bindings and(String name, ValueName.Local binding) {
            Map<String, ValueName.Local> next = new HashMap<>(byName);
            next.put(name, binding);
            return new Bindings(Map.copyOf(next));
        }

        ValueName.Local binderOf(String name) {
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
        unresolved.add(TypeOps.unknownType(n.name(), symbols));
        return TypeName.unresolved(n.written());
    }

    /** Records what a name was answered with, and hands it back. A name with no position was
     * synthesized by an earlier pass rather than written, so there is nothing to point at. */
    private Ast.Name answered(Ast.Name n) {
        if (n.pos() != null) {
            denotations.add(new Denotation(n.name(), n.denotes()));
        }
        return n;
    }
}
