package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

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
 * <p>A name that denotes nothing is reported here and the compile stops, so no later pass sees an
 * unresolved one and none of them needs a null branch. A name a pass synthesized already knowing
 * what it means (a codec {@code Deriver} builds from a field's type) is left as it is.
 */
public final class Resolve {

    private final Symbols symbols;
    /** Every name this pass answered, in the order it met them. */
    private final List<Denotation> denotations = new ArrayList<>();

    private Resolve(Symbols symbols) {
        this.symbols = symbols;
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

    /** A resolved module together with every name the pass answered in it. */
    public record Resolved(Ast.Module module, List<Denotation> denotations) {}

    /** {@code m} with every name it writes resolved against its own definitions — a module compiled
     * with nothing else in sight. */
    public static Ast.Module module(Ast.Module m) {
        return module(m, TypeChecker.symbols(m));
    }

    /** {@code m} with every name it writes resolved against {@code symbols}. */
    public static Ast.Module module(Ast.Module m, Symbols symbols) {
        return resolving(m, symbols).module();
    }

    /** As {@link #module(Ast.Module, Symbols)}, keeping what each name was answered with. */
    public static Resolved resolving(Ast.Module m, Symbols symbols) {
        Resolve r = new Resolve(symbols);
        List<Ast.Def> defs = new ArrayList<>();
        for (Ast.Def def : m.defs()) {
            defs.add(r.def(def));
        }
        List<Ast.BehaviorDef> behaviors = new ArrayList<>();
        for (Ast.BehaviorDef b : m.behaviors()) {
            behaviors.add(switch (b) {
                case Ast.SpecBehavior spec -> new Ast.SpecBehavior(spec.name(), r.params(spec.params()),
                        r.retType(spec.ret()), r.names(spec.constructs()), spec.requires(), spec.pos());
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
                List.copyOf(r.denotations));
    }

    private Ast.FnDef fn(Ast.FnDef f) {
        List<Ast.FnParam> params = new ArrayList<>();
        for (Ast.FnParam p : f.params()) {
            params.add(new Ast.FnParam(p.name(), paramType(p.type()), p.typeFromPattern(), p.pos()));
        }
        return new Ast.FnDef(f.name(), params, retType(f.declaredReturn()), f.intrinsicKey(),
                f.body() == null ? null : expr(f.body()), f.partial(), f.pos());
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
        Ast.TypeRef denoted = resolved.denoting(TypeOps.denoted(resolved, symbols));
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
            case Ast.Data d -> new Ast.Data(d.name(), d.newtype(), names(d.includes()), fields(d.fields()),
                    d.invariant().map(this::expr), d.decoder().map(this::decoder),
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

    private Ast.DecoderDef decoder(Ast.DecoderDef d) {
        return switch (d) {
            case Ast.PrimDecoder p -> new Ast.PrimDecoder(p.from(), p.inputName(), stmts(p.stmts()),
                    construct(p.result()), p.pos());
            case Ast.ObjectDecoder o -> {
                List<Ast.Bind> binds = new ArrayList<>();
                for (Ast.Bind b : o.binds()) {
                    binds.add(new Ast.Bind(b.name(), b.key(), decRef(b.ref()), b.pos()));
                }
                yield new Ast.ObjectDecoder(binds, construct(o.result()), o.pos());
            }
            case Ast.NewtypeDecoder n -> new Ast.NewtypeDecoder(decRef(n.inner()), n.inputName(),
                    construct(n.result()), n.pos());
        };
    }

    private List<Ast.DecStmt> stmts(List<Ast.DecStmt> stmts) {
        List<Ast.DecStmt> out = new ArrayList<>();
        for (Ast.DecStmt s : stmts) {
            out.add(s instanceof Ast.Let let ? new Ast.Let(let.name(), expr(let.value()), let.pos()) : s);
        }
        return out;
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

    private Ast.Construct construct(Ast.Construct c) {
        List<Ast.FieldInit> inits = new ArrayList<>();
        for (Ast.FieldInit i : c.inits()) {
            inits.add(new Ast.FieldInit(i.name(), expr(i.value()), i.pos()));
        }
        return new Ast.Construct(type(c.typeName()), inits, c.spreads(), c.pos());
    }

    // --- encoders ---

    private Ast.EncoderDef encoder(Ast.EncoderDef e) {
        return new Ast.EncoderDef(e.selfName(), rawExpr(e.result()), e.pos());
    }

    private Ast.RawExpr rawExpr(Ast.RawExpr r) {
        return switch (r) {
            case Ast.TextRaw t -> new Ast.TextRaw(expr(t.arg()), t.pos());
            case Ast.IntRaw i -> new Ast.IntRaw(expr(i.arg()), i.pos());
            case Ast.BoolRaw b -> new Ast.BoolRaw(expr(b.arg()), b.pos());
            case Ast.DecimalRaw d -> new Ast.DecimalRaw(expr(d.arg()), d.pos());
            case Ast.IsoTextRaw i -> new Ast.IsoTextRaw(expr(i.arg()), i.pos());
            case Ast.EncodeRaw en -> new Ast.EncodeRaw(type(en.typeName()), expr(en.arg()), en.pos());
            case Ast.ListEnc l -> new Ast.ListEnc(expr(l.source()), encElem(l.elem()), l.pos());
            case Ast.SetEnc s -> new Ast.SetEnc(expr(s.source()), encElem(s.elem()), s.pos());
            case Ast.MapEnc m -> new Ast.MapEnc(expr(m.source()), encElem(m.elem()), encElem(m.key()),
                    m.pos());
            case Ast.OptionRaw o -> new Ast.OptionRaw(expr(o.access()), rawExpr(o.inner()), o.elemVar(),
                    o.pos());
            case Ast.ObjectRaw o -> {
                List<Ast.RawEntry> entries = new ArrayList<>();
                for (Ast.RawEntry entry : o.entries()) {
                    entries.add(new Ast.RawEntry(entry.key(), rawExpr(entry.value()), entry.pos()));
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

    /** Rewrites the names {@code e} itself writes; the recursion into its children is
     * {@link Ast#mapChildren}, so a new expression kind is carried without being named here. */
    private Ast.Expr expr(Ast.Expr e) {
        Ast.Expr mapped = Ast.mapChildren(e, this::expr);
        return switch (mapped) {
            case Ast.NewData nd ->
                    new Ast.NewData(type(nd.typeName()), nd.inits(), nd.spreads(), nd.pos());
            // a binding's pattern may write Option's `Some`, which the binding check then rejects
            // for what it is — a name that opens nothing — rather than as a name nothing declares
            case Ast.LetIn li -> new Ast.LetIn(li.name(), li.value(), paramType(li.declaredType()),
                    li.annotated(),
                    li.opens() == null ? null : caseName(li.opens()),
                    li.body(), li.pos());
            case Ast.Match m -> {
                List<Ast.Case> cases = new ArrayList<>();
                for (Ast.Case c : m.cases()) {
                    cases.add(new Ast.Case(caseNames(c.caseTypes()), c.binding(), c.body(),
                            c.unwrapAsserts() == null ? null : names(c.unwrapAsserts()), c.pos()));
                }
                yield new Ast.Match(m.scrutinee(), cases, m.pos());
            }
            default -> mapped;
        };
    }

    private List<Ast.Expr> exprs(List<Ast.Expr> es) {
        List<Ast.Expr> out = new ArrayList<>();
        for (Ast.Expr e : es) {
            out.add(expr(e));
        }
        return out;
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
            throw TypeOps.unknownType(n.written(), n.pos(), symbols);
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
            throw TypeOps.unknownType(n.written(), n.pos(), symbols);
        }
        return answered(n.denoting(denoted));
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
