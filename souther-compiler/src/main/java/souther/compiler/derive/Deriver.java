package souther.compiler.derive;

import souther.compiler.check.Symbols;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticCode;
import souther.compiler.diag.SourcePos;
import souther.compiler.ast.Ast;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.check.TypeChecker;
import souther.compiler.check.TypeOps;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * Derives default boundary codecs (decoders/encoders and sum discriminators) from the shape
 * of the domain data. Decoders/encoders are not part of the domain syntax (they are a
 * boundary concern); this pass fills them in from field names and types so a domain
 * definition needs only {@code data}/{@code invariant}/{@code behavior}. Conventions:
 * JSON key = field name; single-primitive-field data is a newtype (bare primitive);
 * sum discriminator field = "type", tag = case name.
 */
public final class Deriver {

    private Deriver() {}

    public static Ast.Module derive(Ast.Module module) {
        return derive(module, TypeChecker.symbols(module));
    }

    /** Derives codecs using {@code symbols} for type resolution (own definitions plus any
     * imported ones, for cross-module fields — spec 4). */
    public static Ast.Module derive(Ast.Module module, Symbols symbols) {
        java.util.Set<TypeName> caseNames = new java.util.HashSet<>();
        for (Ast.Def def : symbols.visible()) {
            if (def instanceof Ast.SumData s) {
                caseNames.addAll(TypeOps.caseNames(s));
            }
        }
        List<Ast.Def> defs = new ArrayList<>();
        for (Ast.Def def : module.defs()) {
            defs.add(switch (def) {
                case Ast.Data d -> deriveData(d, symbols, caseNames.contains(symbols.own(d.name())));
                case Ast.SumData s -> deriveSum(s, symbols);
                case Ast.UnitData u -> u;
            });
        }
        return new Ast.Module(module.name(), module.exposing(), module.exposedOutputs(),
                module.imports(), defs, module.behaviors(), module.fns(), module.takenOn(),
                module.examples(), module.fakes(), module.exampleFileTarget(), module.pos());
    }

    private static Ast.Data deriveData(Ast.Data d, Symbols symbols, boolean isCase) {
        Map<String, Type> fields = TypeOps.fieldTypes(d, symbols);
        if (fields.values().stream().anyMatch(t -> t instanceof Type.Erroneous)) {
            // A field whose type nobody could name has no external representation, and saying so
            // would be saying the same thing twice: the name that denotes nothing was reported where
            // it was written. The declaration keeps no codec, which costs nothing — a module holding
            // a type like this is never emitted.
            return d;
        }
        // the decoder and the encoder each read the value under a name of their own, so each owns
        // the bindings it writes rather than sharing the declaration's
        BindingOwner declared = new BindingOwner.OfData(symbols.own(d.name()));
        Optional<Ast.DecoderDef> decoder = d.decoder().isPresent()
                ? d.decoder()
                : Optional.of(deriveDecoder(d, fields, isCase, symbols,
                        new Ast.Binders(new BindingOwner.Synthesized(declared,
                                BindingOwner.Pass.DERIVER, 0))));
        Optional<Ast.EncoderDef> encoder = d.encoder().isPresent()
                ? d.encoder()
                : Optional.of(deriveEncoder(d, fields, isCase,
                        new Ast.Binders(new BindingOwner.Synthesized(declared,
                                BindingOwner.Pass.DERIVER, 1))));
        return new Ast.Data(d.written(), d.newtype(), d.includes(), d.fields(), d.invariants(),
                decoder, encoder, d.pos());
    }

    // --- decoder derivation ---

    private static Ast.DecoderDef deriveDecoder(Ast.Data d, Map<String, Type> fields, boolean isCase,
                                               Symbols symbols, Ast.Binders binders) {
        SourcePos pos = d.pos();
        Ast.Name self = Ast.Name.resolved(symbols.own(d.name()), pos);
        // only an explicit newtype `data X = Y` is bare; a braced record is always an object, even
        // with one field (spec 8.7). A sum case is embedded in the discriminated object, never bare.
        Map.Entry<String, Type> single = bareField(d, fields, isCase);
        if (single != null) {
            Ast.RawKind kind = rawKind(single.getValue());
            Ast.Binder input = binders.binder("__in", pos);
            Ast.Construct result = new Ast.Construct(self,
                    List.of(new Ast.FieldInit(single.getKey(), Ast.Var.local(input, pos), pos)), pos);
            return new Ast.PrimDecoder(kind, input, List.of(), result, pos);
        }
        // a newtype over a non-primitive Y delegates the whole input to Y's decoder (spec 8.7)
        if (d.newtype() && !isCase) {
            Map.Entry<String, Type> only = fields.entrySet().iterator().next();
            Ast.Binder input = binders.binder("__in", pos);
            Ast.Construct result = new Ast.Construct(self,
                    List.of(new Ast.FieldInit(only.getKey(), Ast.Var.local(input, pos), pos)), pos);
            return new Ast.NewtypeDecoder(
                    decRef(only.getValue(), d, only.getKey(), fieldPos(d, only.getKey())),
                    input, result, pos);
        }
        List<Ast.Bind> binds = new ArrayList<>();
        List<Ast.FieldInit> inits = new ArrayList<>();
        for (Map.Entry<String, Type> f : fields.entrySet()) {
            Ast.Binder took = binders.binder(f.getKey(), pos);
            binds.add(new Ast.Bind(took, f.getKey(),
                    decRef(f.getValue(), d, f.getKey(), fieldPos(d, f.getKey())), pos));
            inits.add(new Ast.FieldInit(f.getKey(), Ast.Var.local(took, pos), pos));
        }
        return new Ast.ObjectDecoder(binds, new Ast.Construct(self, inits, pos), pos);
    }

    private static Ast.RawKind rawKind(Type t) {
        if (t == Type.STRING) {
            return Ast.RawKind.TEXT;
        }
        if (t == Type.BOOL) {
            return Ast.RawKind.BOOL;
        }
        if (t == Type.DECIMAL) {
            return Ast.RawKind.DECIMAL;
        }
        if (t == Type.DATE) {
            return Ast.RawKind.DATE;
        }
        if (t == Type.DATETIME) {
            return Ast.RawKind.DATETIME;
        }
        return Ast.RawKind.INT;
    }

    private static Ast.PrimKind primKind(Type t) {
        if (t == Type.STRING) {
            return Ast.PrimKind.STRING;
        }
        if (t == Type.BOOL) {
            return Ast.PrimKind.BOOL;
        }
        if (t == Type.DECIMAL) {
            return Ast.PrimKind.DECIMAL;
        }
        if (t == Type.DATE) {
            return Ast.PrimKind.DATE;
        }
        if (t == Type.DATETIME) {
            return Ast.PrimKind.DATETIME;
        }
        return Ast.PrimKind.INT;
    }

    private static Ast.DecRef decRef(Type t, Ast.Data d, String field, SourcePos pos) {
        if (t == Type.STRING || t == Type.INT || t == Type.BOOL
                || t == Type.DECIMAL || t == Type.DATE || t == Type.DATETIME) {
            return new Ast.PrimDecRef(primKind(t), pos);
        }
        if (t instanceof Type.Ref r) {
            return new Ast.DataDecRef(Ast.Name.resolved(r.name(), pos), pos);
        }
        if (t instanceof Type.ListOf lo) {
            return new Ast.ListDecRef(decRef(lo.element(), d, field, pos), pos);
        }
        if (t instanceof Type.SetOf so) {
            return new Ast.SetDecRef(decRef(so.element(), d, field, pos), pos);
        }
        if (t instanceof Type.OptionOf oo) {
            return new Ast.OptionDecRef(decRef(oo.element(), d, field, pos), pos);
        }
        if (t instanceof Type.MapOf mo) {
            return new Ast.MapDecRef(decRef(mo.value(), d, field, pos), mapKeyDec(mo, d, field, pos), pos);
        }
        throw noCodec(t, d, field, pos);
    }

    // --- encoder derivation ---

    private static Ast.EncoderDef deriveEncoder(Ast.Data d, Map<String, Type> fields, boolean isCase,
                                                Ast.Binders binders) {
        SourcePos pos = d.pos();
        Ast.Binder self = binders.binder("self", pos);
        Map.Entry<String, Type> single = bareField(d, fields, isCase);
        if (single != null) {
            Ast.Expr access = new Ast.FieldAccess(Ast.Var.local(self, pos), single.getKey(), pos);
            return new Ast.EncoderDef(self, primRaw(single.getValue(), access, pos), pos);
        }
        // a newtype over a non-primitive Y encodes self.value as Y writes itself — Y's
        // representation, not `{value: ...}` (spec 8.7). Y is a named data, a sum, or a collection,
        // so this is the same choice a field of type Y makes.
        if (d.newtype() && !isCase) {
            Map.Entry<String, Type> only = fields.entrySet().iterator().next();
            Ast.Expr access = new Ast.FieldAccess(Ast.Var.local(self, pos), only.getKey(), pos);
            return new Ast.EncoderDef(self,
                    rawForAccess(only.getValue(), access, d, only.getKey(), pos, binders), pos);
        }
        List<Ast.RawEntry> entries = new ArrayList<>();
        for (Map.Entry<String, Type> f : fields.entrySet()) {
            entries.add(new Ast.RawEntry(f.getKey(),
                    rawFor(f.getValue(), f.getKey(), d, fieldPos(d, f.getKey()), self, binders), pos));
        }
        return new Ast.EncoderDef(self, new Ast.ObjectRaw(entries, pos), pos);
    }

    private static Ast.RawExpr primRaw(Type t, Ast.Expr access, SourcePos pos) {
        if (t == Type.STRING) {
            return new Ast.TextRaw(access, pos);
        }
        if (t == Type.BOOL) {
            return new Ast.BoolRaw(access, pos);
        }
        if (t == Type.DECIMAL) {
            return new Ast.DecimalRaw(access, pos);
        }
        if (t == Type.DATE || t == Type.DATETIME) {
            return new Ast.IsoTextRaw(access, pos);
        }
        return new Ast.IntRaw(access, pos);
    }

    private static boolean isPrim(Type t) {
        return t == Type.STRING || t == Type.INT || t == Type.BOOL
                || t == Type.DECIMAL || t == Type.DATE || t == Type.DATETIME;
    }

    private static Ast.RawExpr rawFor(Type t, String field, Ast.Data d, SourcePos pos,
                                      Ast.Binder self, Ast.Binders binders) {
        return rawForAccess(t, new Ast.FieldAccess(Ast.Var.local(self, pos), field, pos),
                d, field, pos, binders);
    }

    private static Ast.RawExpr rawForAccess(Type t, Ast.Expr access, Ast.Data d, String field,
                                            SourcePos pos, Ast.Binders binders) {
        if (isPrim(t)) {
            return primRaw(t, access, pos);
        }
        if (t instanceof Type.Ref r) {
            return new Ast.EncodeRaw(Ast.Name.resolved(r.name(), pos), access, pos);
        }
        if (t instanceof Type.ListOf lo) {
            return new Ast.ListEnc(access, encElem(lo.element(), d, field, pos), pos);
        }
        if (t instanceof Type.SetOf so) {
            return new Ast.SetEnc(access, encElem(so.element(), d, field, pos), pos);
        }
        if (t instanceof Type.OptionOf oo) {
            Ast.Binder elem = binders.binder("$opt", pos);
            Ast.RawExpr inner = rawForAccess(oo.element(), Ast.Var.local(elem, pos), d, field, pos,
                    binders);
            return new Ast.OptionRaw(access, inner, elem, pos);
        }
        if (t instanceof Type.MapOf mo) {
            return new Ast.MapEnc(access, encElem(mo.value(), d, field, pos), mapKeyEnc(mo, d, field, pos), pos);
        }
        throw noCodec(t, d, field, pos);
    }

    /**
     * How a map's keys cross the boundary. A JSON object's keys are strings, so a key is decoded from
     * and encoded to a bare string: a {@code String} key passes through, a String-backed newtype
     * ({@code Map<商品ID, V>}) is constructed on decode (its invariant enforced) and rendered bare on
     * encode, and a temporal key is parsed from and written as its ISO form — the same representation
     * a {@code Date} field already has. Any other key type is rejected before here (ADR-0040).
     */
    private static Ast.DecRef mapKeyDec(Type.MapOf mo, Ast.Data d, String field, SourcePos pos) {
        if (mo.key() instanceof Type.Ref r) {
            return new Ast.DataDecRef(Ast.Name.resolved(r.name(), pos), pos);
        }
        if (mo.key() == Type.STRING || mo.key() == Type.DATE || mo.key() == Type.DATETIME) {
            return new Ast.PrimDecRef(primKind(mo.key()), pos);
        }
        throw badMapKey(mo.key(), d, field, pos);
    }

    private static Ast.EncElem mapKeyEnc(Type.MapOf mo, Ast.Data d, String field, SourcePos pos) {
        if (mo.key() instanceof Type.Ref r) {
            return new Ast.DataEnc(Ast.Name.resolved(r.name(), pos), pos);
        }
        if (mo.key() == Type.STRING || mo.key() == Type.DATE || mo.key() == Type.DATETIME) {
            return new Ast.PrimEnc(primKind(mo.key()), pos);
        }
        throw badMapKey(mo.key(), d, field, pos);
    }

    /**
     * A key that cannot key a JSON object. Derivation runs ahead of the checker that makes the same
     * judgement on a data's fields, so it reports the same way rather than as a codec that gave up:
     * the reader has to change the key type either way, and being told twice in two vocabularies
     * helps nobody.
     */
    private static CompileException badMapKey(Type key, Ast.Data d, String field, SourcePos pos) {
        return CompileException.of(
                Diagnostic.of(DiagnosticCode.E1314, "check.map.key.field")
                        .at(pos).args(where(d, field), Type.show(key))
                        .hint("check.map.key.field.hint").build(),
                "a Map crossing the boundary at `" + where(d, field) + "` must be keyed by String, a"
                        + " String-backed newtype (`data X = String`), Date or DateTime, got "
                        + Type.show(key));
    }

    /** How to name the place a boundary complaint belongs to. A newtype's single field is implicit —
     * the author wrote {@code data X = Y}, never a field called {@code value} — so it is named by
     * the type alone. */
    private static String where(Ast.Data d, String field) {
        return d.newtype() ? d.name() : d.name() + "." + field;
    }

    /** The encoder for one element of a collection. A collection may hold a collection
     * ({@code Map<String, List<商品ID>>}), so this recurses the same way {@link #decRef} does on the
     * decoding side — the two stay symmetric, and what decodes in encodes back out. */
    private static Ast.EncElem encElem(Type t, Ast.Data d, String field, SourcePos pos) {
        if (isPrim(t)) {
            return new Ast.PrimEnc(primKind(t), pos);   // every primitive has a leaf encoder
        }
        if (t instanceof Type.Ref r) {
            return new Ast.DataEnc(Ast.Name.resolved(r.name(), pos), pos);
        }
        if (t instanceof Type.ListOf lo) {
            return new Ast.ListElemEnc(encElem(lo.element(), d, field, pos), pos);
        }
        if (t instanceof Type.SetOf so) {
            return new Ast.SetElemEnc(encElem(so.element(), d, field, pos), pos);
        }
        if (t instanceof Type.MapOf mo) {
            return new Ast.MapElemEnc(encElem(mo.value(), d, field, pos), mapKeyEnc(mo, d, field, pos), pos);
        }
        throw noCodec(t, d, field, pos);
    }

    /**
     * The one report for a field whose type has no boundary representation, wherever in the type it
     * sits: it names the field and prints the type as it was written
     * ({@code Map<String, (String, Int)>}), and it is positioned on the field rather than on the
     * data, so the caret lands on what has to change. The message says what is unrepresentable — a
     * tuple has no field names to write — rather than naming the codec that gave up.
     */
    private static CompileException noCodec(Type t, Ast.Data d, String field, SourcePos pos) {
        if (t instanceof Type.TupleOf) {
            return CompileException.of(
                    Diagnostic.of(DiagnosticCode.E1311, "check.derive.tuplefield")
                            .at(pos).args(where(d, field), Type.show(t)).build(),
                    "`" + where(d, field) + "` is " + Type.show(t) + ": a tuple has"
                            + " no external representation, so no codec can be derived (ADR-0036)."
                            + " Use a named data.");
        }
        return CompileException.of(
                Diagnostic.of(DiagnosticCode.E1311, "check.derive.nocodec")
                        .at(pos).args(where(d, field), Type.show(t)).build(),
                "no codec can be derived for `" + where(d, field) + "`: "
                        + Type.show(t) + " has no external representation");
    }

    /** Where the field was written, for a diagnostic to point at. A field a data takes in through
     * {@code ...Included} was written elsewhere, so that one falls back to the data itself. */
    private static SourcePos fieldPos(Ast.Data d, String field) {
        for (Ast.Field f : d.fields()) {
            if (f.name().equals(field)) {
                return f.pos();
            }
        }
        return d.pos();
    }

    // --- sum derivation ---

    private static Ast.SumData deriveSum(Ast.SumData s, Symbols symbols) {
        List<Ast.Name> leaves = leafCases(s, symbols);
        Optional<Ast.Discriminate> decoder = s.decoder().isPresent()
                ? s.decoder()
                : Optional.of(new Ast.Discriminate("type", tagVariants(s, leaves), s.pos()));
        Optional<Ast.SumEncoder> encoder = s.encoder().isPresent()
                ? s.encoder()
                : Optional.of(new Ast.SumEncoder("type", encVariants(s, leaves), s.pos()));
        return new Ast.SumData(s.written(), s.cases(), decoder, encoder, s.pos());
    }

    /**
     * The cases a derived codec dispatches over, with nested sums folded to their leaves —
     * `費用負担区分 = 自社負担 | 先方負担` where `自社負担 = 立替 | 仮払い | 会社カード` dispatches over
     * 立替 / 仮払い / 会社カード / 先方負担 (spec 8.3, 10.3).
     *
     * <p>Folding is what makes a nested sum round-trip. Tagging the direct case instead would put
     * two levels on one `"type"` key: the outer encoder wrote {@code {type: 自社負担}}, losing
     * which leaf it was, and the inner decoder then rejected that same tag.
     */
    private static List<Ast.Name> leafCases(Ast.SumData s, Symbols symbols) {
        List<Ast.Name> leaves = new ArrayList<>();
        collectLeafCases(s, symbols, leaves);
        return leaves;
    }

    private static void collectLeafCases(Ast.SumData s, Symbols symbols, List<Ast.Name> out) {
        collectLeafCases(s, symbols, out, new java.util.HashSet<>());
    }

    private static void collectLeafCases(Ast.SumData s, Symbols symbols, List<Ast.Name> out,
                                         java.util.Set<String> visiting) {
        if (!visiting.add(s.name())) {
            return;   // a sum that reaches itself; DataChecker reports it, this only has to terminate
        }
        for (Ast.Name caseName : s.cases()) {
            if (symbols.get(caseName.denotes()) instanceof Ast.SumData nested) {
                collectLeafCases(nested, symbols, out, visiting);
            } else if (!out.contains(caseName)) {
                out.add(caseName);
            }
        }
    }

    private static List<Ast.Variant> tagVariants(Ast.SumData s, List<Ast.Name> cases) {
        List<Ast.Variant> variants = new ArrayList<>();
        for (Ast.Name caseName : cases) {
            variants.add(new Ast.Variant(caseName.denotes().name(), caseName, s.pos()));
        }
        return variants;
    }

    private static List<Ast.EncVariant> encVariants(Ast.SumData s, List<Ast.Name> cases) {
        List<Ast.EncVariant> variants = new ArrayList<>();
        for (Ast.Name caseName : cases) {
            variants.add(new Ast.EncVariant(caseName, caseName.denotes().name(), s.pos()));
        }
        return variants;
    }

    /**
     * The bare inner field of an explicit newtype {@code data X = Y} whose {@code Y} is primitive
     * (spec 8.7). A braced record is always an object — even a single-field one — so newtype-ness
     * is decided by the {@code = Y} syntax, not the shape; a sum case is never bare either.
     */
    private static Map.Entry<String, Type> bareField(Ast.Data d, Map<String, Type> fields, boolean isCase) {
        if (!d.newtype() || isCase) {
            return null;
        }
        Map.Entry<String, Type> only = fields.entrySet().iterator().next();
        return isPrim(only.getValue()) ? only : null;
    }
}
