package souther.compiler;

import souther.compiler.ast.Ast;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What a value looks like in the form a derived decoder reads — the *neutral* form an {@code example}
 * fixture is written in, and the one thing both directions of a row have to agree on.
 *
 * <p>A row reaches that form two ways. From what the author wrote, which {@link ExampleVerifier} walks:
 * a literal, a record, a collection, a newtype application. And from a value a helper returned
 * (ADR-0077), which {@link #of} re-materialises. The rules that decide the form itself — which
 * discriminator a case of a sum carries, when a unit case travels as a bare name, which written list is
 * a map's entries — are the same rules whichever direction arrives at them, so they are here rather
 * than restated on one side and read from the other.
 *
 * <p>Nothing here knows about the JVM classes an example runs against ({@link HelperInvoker} does) or
 * about diagnostics: a form that cannot be reached is a {@link FixtureException}, which the row reports.
 */
final class NeutralForm {

    private final Symbols symbols;

    NeutralForm(Symbols symbols) {
        this.symbols = symbols;
    }

    // --- a live value, re-materialised -------------------------------------------------------------

    /**
     * A value a helper returned, in the neutral form a fixture is written in.
     *
     * <p>The inverse of writing the fixture, directed by the declared types: a scalar and a temporal are
     * already their own neutral form, a collection is re-materialised element by element, and a data is
     * read field by field through the accessor every data has (ADR-0065), each field against its
     * declared type, carrying the discriminator its sum's decoder reads — which is what a written record
     * fixture is built as, so one decoder reads both. An empty optional is left out, as writing
     * {@code None} leaves it out.
     *
     * <p>Not the derived {@code encoder()}: that answers what the boundary reads, which is a different
     * question. A {@code Date}'s neutral form is the parsed temporal while its encoder writes ISO text,
     * so a newtype over a date came back as text its own decoder refuses.
     *
     * @param helper the helper that produced the value, for the reason a row is given when it cannot be
     *               read back
     */
    Object of(Object live, Type position, String helper) {
        if (live == null) {
            return live;
        }
        if (isScalar(live)) {
            // A scalar is already its own neutral form, except that a temporal's is the parsed value
            // and text is what a boundary carries one as. Asked here rather than left to the decoder,
            // which reads that text too and would take a helper's `String` for a date-time.
            if (live instanceof String text && temporalUnder(position) instanceof Type.Prim temporal) {
                throw notWrittenAsATemporal(temporal, text);
            }
            return live;
        }
        Type opened = open(position);
        if (live instanceof Map<?, ?> m) {
            Type key = opened instanceof Type.MapOf map ? map.key() : null;
            Type value = opened instanceof Type.MapOf map ? map.value() : null;
            Map<Object, Object> out = new LinkedHashMap<>();
            for (Map.Entry<?, ?> e : m.entrySet()) {
                out.put(of(e.getKey(), key, helper), of(e.getValue(), value, helper));
            }
            return out;
        }
        if (live instanceof Iterable<?> it) {
            Type element = elementOf(opened);
            List<Object> out = new ArrayList<>();
            for (Object e : it) {
                out.add(of(e, element, helper));
            }
            return out;
        }
        String name = simpleName(live);
        // An optional field holds an `Option`: `None` is the absent value a fixture writes by leaving
        // the field out, and `Some` holds what the position's own type reads (spec §absence-is-written-as-null).
        if (name.equals("Option$None")) {
            return null;
        }
        if (name.equals("Option$Some")) {
            return of(field(live, "value", helper), opened, helper);
        }
        TypeName caseName = symbols.resolve(name);
        if (caseName == null) {
            throw new FixtureException("`" + helper + "` returned a " + name
                    + ", which is not a type this example can read");
        }
        if (!(symbols.get(caseName) instanceof Ast.Data data)) {
            // a unit case: its name where the position reads one, else the tag its sum's decoder reads
            if (readsABareName(position, caseName)) {
                return caseName.name();
            }
            Map<String, Object> unit = new LinkedHashMap<>();
            tagged(caseName, unit);
            return unit;
        }
        if (data.newtype()) {
            Type base = shapeOf(newtypeBaseType(caseName));
            return newtypeAt(position, caseName, name,
                    shaped(of(field(live, "value", helper), base, helper), base));
        }
        Map<String, Ast.TypeRef> declared = fieldTypes(caseName);
        Map<String, Object> out = new LinkedHashMap<>();
        for (Map.Entry<String, Ast.TypeRef> f : declared.entrySet()) {
            Type type = shapeOf(f.getValue());
            Object value = shaped(of(field(live, f.getKey(), helper), type, helper), type);
            // an absent optional is left out, the same neutral form a fixture writes for `None`
            if (value != null) {
                out.put(f.getKey(), value);
            }
        }
        tagged(caseName, out);
        return out;
    }

    /** One field of a live data, read through the accessor every data has (ADR-0065). Its class may be
     * package-private, so the declared method is taken and opened, as a codec is. */
    private Object field(Object live, String name, String helper) {
        try {
            java.lang.reflect.Method accessor = live.getClass().getDeclaredMethod(name);
            accessor.setAccessible(true);
            return accessor.invoke(live);
        } catch (ReflectiveOperationException _) {
            throw new FixtureException("the value `" + helper + "` returned cannot be read back as a"
                    + " fixture: `" + simpleName(live) + "` has no `" + name + "` to read");
        }
    }

    // --- the form itself, read by both directions -------------------------------------------------

    /**
     * A newtype case read through its sum decodes from the adjacent form that sum's decoder reads —
     * the inner value under {@code value}, next to the discriminator (spec §sum-discrimination) — while a fixture
     * names the case the way the domain constructs it,
     * {@code アクティベート済み(メールアドレス("a@example.com"))}. Wrap it here, as a product case's
     * field map and a unit case's name are wrapped; a newtype no sum lists is its bare inner value,
     * unchanged.
     */
    private Object adjacentlyTagged(String caseName, Object inner) {
        Map<String, Object> tagged = new LinkedHashMap<>();
        tagged(caseName, tagged);
        if (tagged.isEmpty()) {
            return inner;   // not a case of any sum: the newtype's own form is its inner value
        }
        tagged.put("value", inner);
        return tagged;
    }

    /**
     * Writes the discriminator a sum's decoder reads, when the data is a case of one.
     * A fixture names the case it means — `予算枠 = 未定予算`, or a whole `プロジェクト依頼 { … }` where
     * the parameter is the sum `依頼` — the same way the domain writes a construction, while the
     * decoder that reads it wants a tag on a key. Where the case is read as itself rather than
     * through its sum, the tag is a field the decoder does not look at.
     *
     * <p>A field the fixture wrote itself is never replaced. A case whose own field is named like its
     * sum's discriminator is already ambiguous at the boundary — the case encoder and the sum encoder
     * both claim that key — and overwriting here would hide that behind an example that passes while
     * decoding something the author did not write. Leaving the written value in place makes the row
     * fail on the tag it cannot match, which is the honest outcome.
     */
    void tagged(String written, Map<String, Object> map) {
        TypeName caseName = symbols.resolve(written);
        if (caseName != null) {
            tagged(caseName, map);
        }
    }

    void tagged(TypeName caseName, Map<String, Object> map) {
        for (Ast.Def def : symbols.visible()) {
            if (!(def instanceof Ast.SumData sum) || sum.decoder().isEmpty()) {
                continue;
            }
            for (Ast.Variant variant : sum.decoder().get().variants()) {
                if (caseName.equals(variant.caseType().denotes())) {
                    map.putIfAbsent(sum.decoder().get().key(), variant.tag());
                    return;
                }
            }
        }
    }

    /** Gives a value the neutral shape its declared type decodes from. A {@code Map} is written as a
     * list of {@code (key, value)} pairs — Elm's {@code Dict.fromList}, and the same list literal a
     * {@code Set} takes — while the decoder wants a map, so the pairs are collected here. Everything
     * else passes through; a {@code List} written as a list stays one, since the declared type, not the
     * literal, decides. Read on the checked type, so it applies wherever a value is decoded: a field of
     * a record fixture, and a behavior's argument or output. */
    Object shaped(Object v, Type type) {
        if (type == null || v == null) {
            return v;
        }
        if (type instanceof Type.MapOf map && v instanceof List<?> entries) {
            Map<Object, Object> m = new LinkedHashMap<>();
            for (Object entry : entries) {
                if (!(entry instanceof List<?> pair) || pair.size() != 2) {
                    throw new FixtureException("a `Map` fixture is a list of (key, value) pairs,"
                            + " e.g. [ (\"apple\", 3) ]");
                }
                // Both sides. A key is a position of the same kind as a value, so an inner
                // collection written in key position is the neutral form of that collection
                // and not the list of pairs it was written as.
                m.put(shaped(pair.get(0), map.key()), shaped(pair.get(1), map.value()));
            }
            return m;
        }
        if (v instanceof List<?> elements) {
            Type element = switch (type) {
                case Type.ListOf l -> l.element();
                case Type.SetOf s -> s.element();
                default -> null;
            };
            if (element != null) {
                List<Object> out = new ArrayList<>(elements.size());
                for (Object e : elements) {
                    out.add(shaped(e, element));
                }
                return out;
            }
        }
        return v;
    }

    /** Whether the position names this type itself rather than a sum that lists it. Read as itself, a
     *  newtype's form is its inner value — what its own decoder reads — and what some other
     *  declaration does with the type does not reach here. */
    private boolean readsAsItself(Type position, TypeName caseName) {
        return open(position) instanceof Type.Ref r && caseName.equals(r.name());
    }

    /**
     * A newtype's neutral form at the position it is written in: its inner value, wearing the envelope
     * only where the position reads it through a sum that lists it.
     *
     * <p>The {@code "value"} envelope is not part of a newtype's representation — it is what
     * membership adds, which is why a standalone newtype is bare (spec §sum-discrimination). So the position decides
     * it, the way it decides whether a unit case travels as a bare name, and what some other
     * declaration does with the type does not reach a fixture written at the type itself.
     */
    /**
     * As below, for a case already resolved. A name spelled here would have to be one
     * {@link Symbols#resolve} answers to, which an imported type's declared name is not.
     */
    Object newtypeAt(Type position, TypeName caseName, Object inner) {
        if (readsAsItself(position, caseName)) {
            return inner;
        }
        Map<String, Object> envelope = new LinkedHashMap<>();
        tagged(caseName, envelope);
        if (envelope.isEmpty()) {
            return inner;   // not a case of any sum: the newtype's own form is its inner value
        }
        envelope.put("value", inner);
        return envelope;
    }

    /**
     * A value already in the neutral form of {@code from}, read at {@code to}.
     *
     * <p>A neutral form is decided by a position and not only by a type: a newtype is bare where the
     * position reads it as itself and wears the envelope where the position is a sum that lists it
     * (<<sum-discrimination>>). So a value that was built at one position and now stands at another
     * is written the way the second one reads, and a collection's elements move with it.
     *
     * <p>Only the widening direction has to be answered, because it is the only one admission lets
     * through: a case reaches a position typed by a sum that lists it, never the other way.
     */
    Object reread(Object value, Type from, Type to) {
        if (value == null || from == null || to == null || from.equals(to)) {
            return value;
        }
        if (from instanceof Type.OptionOf a) {
            return reread(value, a.element(), to instanceof Type.OptionOf b ? b.element() : to);
        }
        if (to instanceof Type.OptionOf b) {
            return reread(value, from, b.element());
        }
        if (sequenceElementOf(from) instanceof Type a && sequenceElementOf(to) instanceof Type b
                && value instanceof List<?> elements) {
            List<Object> out = new ArrayList<>(elements.size());
            for (Object each : elements) {
                out.add(reread(each, a, b));
            }
            return out;
        }
        if (from instanceof Type.MapOf a && to instanceof Type.MapOf b
                && value instanceof Map<?, ?> entries) {
            Map<Object, Object> out = new LinkedHashMap<>();
            for (Map.Entry<?, ?> each : entries.entrySet()) {
                out.put(reread(each.getKey(), a.key(), b.key()),
                        reread(each.getValue(), a.value(), b.value()));
            }
            return out;
        }
        if (from instanceof Type.Ref r && isNewtype(r.name())) {
            // Bare here, because `from` is the newtype's own reference and reads it as itself.
            return newtypeAt(to, r.name(), value);
        }
        return value;
    }

    /** The element a list or a set holds, or null where the type holds neither. Narrower than
     *  {@link #elementOf}, which opens an optional and reads a map's entry as a pair. */
    private static Type sequenceElementOf(Type type) {
        return type instanceof Type.ListOf l ? l.element()
                : type instanceof Type.SetOf s ? s.element() : null;
    }

    Object newtypeAt(Type position, TypeName caseName, String written, Object inner) {
        return readsAsItself(position, caseName) ? inner : adjacentlyTagged(written, inner);
    }

    /** As above, for a construction written as a call, where the name is what the row spelled. */
    Object newtypeAt(Type position, String written, Object inner) {
        return newtypeAt(position, symbols.resolve(written), written, inner);
    }

    /** Whether the position this case is written in reads a bare name: it is typed as an enumeration,
     * or it is untyped here and every sum that lists the case is one. */
    boolean readsABareName(Type expected, TypeName caseName) {
        Type position = open(expected);
        return position != null
                ? TypeOps.isUnitOnlySum(position, symbols)
                : onlyEnumerationsList(caseName);
    }

    /** Whether every sum that lists this case is an enumeration, so its neutral form is its name
     * wherever it is written. Asked only where the position has no declared type to read it as. */
    private boolean onlyEnumerationsList(TypeName caseName) {
        boolean listed = false;
        for (Ast.Def def : symbols.visible()) {
            if (!(def instanceof Ast.SumData sum) || sum.decoder().isEmpty()) {
                continue;
            }
            for (Ast.Variant variant : sum.decoder().get().variants()) {
                if (caseName.equals(variant.caseType().denotes())) {
                    if (!TypeOps.isUnitOnlySum(sum, symbols)) {
                        return false;
                    }
                    listed = true;
                }
            }
        }
        return listed;
    }

    /** A data's fields by name, following the `...includes` it composes in (spec §data). */
    Map<String, Ast.TypeRef> fieldTypes(TypeName typeName) {
        Map<String, Ast.TypeRef> out = new LinkedHashMap<>();
        if (symbols.get(typeName) instanceof Ast.Data d) {
            for (Ast.Name inc : d.includes()) {
                out.putAll(fieldTypes(inc.denotes()));
            }
            for (Ast.Field f : d.fields()) {
                // an example builds its input through a decoder, so a field with no external
                // representation is not one it can state; the data declaration refused it already
                if (f.type() instanceof Ast.TypeRef ref) {
                    out.put(f.name(), ref);
                }
            }
        }
        return out;
    }

    /**
     * The declared type of a field, used only to shape the written value (a map's entry pairs, a
     * set's list). The {@code TypeRef} comes from the module that declares the data, and it says what
     * it denotes — resolved where it was written, so naming a type this module never imported is not
     * a question asked here at all (issue #110 was that question being asked, and answered with the
     * declaring file's position).
     */
    Type shapeOf(Ast.TypeRef declaredType) {
        return declaredType == null ? null : declaredType.denotes();
    }

    boolean isNewtype(String name) {
        return symbols.declaration(name) instanceof Ast.Data d && d.newtype();
    }

    /** As above, for a name that has already been resolved — an imported value's body names its own
     * module's types, which the module reading the row need not have imported. */
    boolean isNewtype(TypeName name) {
        return name != null && symbols.get(name) instanceof Ast.Data d && d.newtype();
    }

    /** The written form of what a newtype wraps, kept whole so a generic base
     * ({@code data 在庫 = Map<商品ID, Int>}) keeps its type arguments. */
    Ast.TypeRef newtypeBaseType(String name) {
        return symbols.declaration(name) instanceof Ast.Data d && d.newtype() && d.fields().size() == 1
                && d.fields().get(0).type() instanceof Ast.TypeRef base
                ? base
                : null;
    }

    /** As above, for a name that has already been resolved. */
    Ast.TypeRef newtypeBaseType(TypeName name) {
        return name != null && symbols.get(name) instanceof Ast.Data d && d.newtype()
                && d.fields().size() == 1 && d.fields().get(0).type() instanceof Ast.TypeRef base
                ? base : null;
    }

    // --- reading a position's type ----------------------------------------------------------------

    /** What a written list holds, when the position says: a list's or a set's element, or a map's
     * entry pair. An optional is opened first — writing a value for a `T?` field writes a `T`. */
    static Type elementOf(Type expected) {
        return switch (open(expected)) {
            case Type.ListOf l -> l.element();
            case Type.SetOf s -> s.element();
            case Type.MapOf m -> Type.tuple(List.of(m.key(), m.value()));
            case null, default -> null;
        };
    }

    /** The types of a written tuple's parts, or null when the position does not say. A map's entry is
     * the pair that carries its key type, which is where an enumeration key is written. */
    static List<Type> entryTypes(Type expected, int arity) {
        Type opened = open(expected);
        if (opened instanceof Type.MapOf m && arity == 2) {
            return List.of(m.key(), m.value());
        }
        if (opened instanceof Type.TupleOf t && t.elements().size() == arity) {
            return t.elements();
        }
        return null;
    }

    static Type open(Type t) {
        return t instanceof Type.OptionOf o ? open(o.element()) : t;
    }

    /**
     * The temporal {@code position} is, through whatever stands between — an optional holds the value
     * itself, a newtype wraps what it is written from — or null where it is not a temporal at all.
     *
     * <p>A date is written {@code Date("2026-07-25")} and a date-time {@code DateTime("…")}, and the
     * compiler parses the text where it stands, so a temporal is already parsed by the time it is a
     * fixture. The derived decoders read ISO text as well, because that is how one crosses a boundary,
     * and what a boundary carries a value as is not a second way to write a fixture.
     *
     * <p>Here because both directions a row reaches the neutral form by have to ask it: what the
     * author wrote, and what a helper returned. Stated on one side and read from the other, the two
     * would answer differently about the same position.
     */
    Type.Prim temporalUnder(Type position) {
        Set<TypeName> through = new LinkedHashSet<>();
        Type at = open(position);
        while (true) {
            if (at instanceof Type.Prim prim) {
                // Which primitives are temporal is asked of each one, so a primitive added later is
                // answered at its declaration rather than falling into the "not a temporal" side of
                // a comparison nobody revisited.
                return switch (prim) {
                    case DATE, TIME, DATETIME, INSTANT -> prim;
                    case INT, STRING, BOOL, DECIMAL, RAW -> null;
                };
            }
            if (!(at instanceof Type.Ref ref) || !through.add(ref.name())) {
                return null;
            }
            Ast.TypeRef base = newtypeBaseType(ref.name());
            if (base == null) {
                return null;
            }
            at = open(shapeOf(base));
        }
    }

    /**
     * Refuses a value that is not in the form a fixture writes at {@code position}, without reading it
     * back.
     *
     * <p>For where nothing encloses a helper's application — the whole of an expected value, or the
     * whole of a stand-in — and the value it answered with is taken as it stands rather than
     * re-materialised ({@link #of}). Being unable to read a value back is not the same as its form
     * being wrong, and only the second is a rule, so this holds the rule and asks nothing else.
     *
     * <p>The rule is {@link #temporalUnder}'s, and a container is walked because a position's element
     * type is part of what it says: a written {@code [ "…" ]} at a {@code List<DateTime>} is refused
     * where the element type travels with it, and a helper answering with that same list is the same
     * fixture. The walk stops at anything nominal — a generated value's fields are the types they were
     * declared as, so there is nothing there a fixture could have written wrongly.
     */
    void requireWrittenForm(Object live, Type position) {
        if (live instanceof String text && temporalUnder(position) instanceof Type.Prim temporal) {
            throw notWrittenAsATemporal(temporal, text);
        }
        Type opened = open(position);
        if (live instanceof Map<?, ?> entries && opened instanceof Type.MapOf map) {
            for (Map.Entry<?, ?> e : entries.entrySet()) {
                requireWrittenForm(e.getKey(), map.key());
                requireWrittenForm(e.getValue(), map.value());
            }
            return;
        }
        Type element = elementOf(opened);
        if (element != null && live instanceof Iterable<?> elements) {
            for (Object e : elements) {
                requireWrittenForm(e, element);
            }
        }
    }

    /** What a fixture that wrote text where a temporal stands is told, wherever it wrote it. */
    static FixtureException notWrittenAsATemporal(Type.Prim temporal, String text) {
        return new FixtureException("a `" + temporal.shown() + "` is written `" + temporal.shown()
                + "(\"" + text + "\")`; a string is how one arrives from outside, not how a fixture"
                + " writes it");
    }

    /** Whether a live value is the absent optional. */
    static boolean isAbsent(Object live) {
        return live != null && simpleName(live).equals("Option$None");
    }

    /** What a live optional holds. A `?` position takes the value itself as well as a `Some` around
     *  it, so anything that is not one is what it stands for. */
    static Object heldBy(Object live) {
        if (live == null || !simpleName(live).equals("Option$Some")) {
            return live;
        }
        try {
            java.lang.reflect.Method accessor = live.getClass().getDeclaredMethod("value");
            accessor.setAccessible(true);
            return accessor.invoke(live);
        } catch (ReflectiveOperationException _) {
            throw new FixtureException("an optional's value cannot be read back: `"
                    + simpleName(live) + "` has no `value` to read");
        }
    }

    /** Whether a value is a neutral scalar, so it can be shown as written rather than by class name. */
    static boolean isScalar(Object v) {
        return v instanceof String || v instanceof Long || v instanceof Boolean
                || v instanceof BigDecimal || v instanceof java.time.LocalDate
                || v instanceof java.time.LocalTime || v instanceof java.time.LocalDateTime
                || v instanceof java.time.Instant;
    }

    /** The case name a live value carries: its class's simple name, which is the type's own name. */
    static String simpleName(Object o) {
        if (o == null) {
            return "null";
        }
        String n = o.getClass().getName();
        int dot = n.lastIndexOf('.');
        return dot < 0 ? n : n.substring(dot + 1);
    }
}
