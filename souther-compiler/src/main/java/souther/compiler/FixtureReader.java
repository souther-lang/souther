package souther.compiler;

import souther.compiler.ast.Ast;
import souther.compiler.check.CallElaborator;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.observe.Limits;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.types.ValueName;
import souther.runtime.Sets;

import net.unit8.raoh.Err;
import net.unit8.raoh.Issues;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Result;
import net.unit8.raoh.decode.Decoder;
import net.unit8.raoh.decode.ObjectDecoders;

import java.math.BigDecimal;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Reads a written fixture as the value it states, against the type of the position it is written in.
 *
 * <p>One reading, and only one. A fixture applies helpers (ADR-0077), and a {@code partial} one may
 * not stop — so a reading is held to a budget, and a worker that runs out of it is asked to stop and
 * cannot be made to: a fixture reaches no interrupt point, so it may still be inside
 * {@link #expandedValue} holding a binding or a half-walked expansion. An instance is therefore one
 * row's, or one written statement's, and is dropped when that reading ends. Nothing it can still
 * write to — {@link #bindings}, {@link #expanding}, the helper {@link HelperInvoker#running()} names
 * — is read by the reading after it.
 *
 * <p>What a reading cannot build, and what did not finish, are a {@link FixtureException} and a
 * {@link StackExhaustedException}. Which diagnostic either becomes, and what a budget is, are not
 * here: this class has no {@code Diagnostic}, no {@code SourceRef}, and no worker of its own. The
 * row evaluation ({@link ExampleVerifier}) and the reading of a module's written statements each say
 * what a failure means where they are, and they say different things about the same one.
 *
 * <p>Showing a value is here too, though it is not reading one. It needs the generated encoders, the
 * loader and the built value, and both readers above need it — left in either, the other would grow
 * a second copy.
 *
 * <p>Public for one thing only: {@link Construction}, which the adequacy report asks to find out
 * whether a value composed elsewhere builds at this module's boundary. That is this class's own
 * question — putting a value through the decoder a row's fixture goes through is the whole of the
 * answer — and it used to be asked of a row evaluator built with signatures, requirements and a
 * budget it had no rows to spend. Everything else here is package-private, and the constructor is:
 * a reading belongs to whichever of the two readers above started it.
 */
public final class FixtureReader {

    private final Ast.Module module;
    private final Symbols symbols;
    /** The values a row may name: this module's own, and the ones its imports bring in. */
    private final Map<String, Ast.FnDef> values;
    private final MemoryClassLoader loader;
    /** Runs a helper a fixture applies. One reading's, because what it is running is one reading's. */
    private final HelperInvoker helpers;
    /** What a value looks like in the form a decoder reads — the rules both directions of a row read. */
    private final NeutralForm neutral;

    FixtureReader(Ast.Module module, Symbols symbols, Map<String, Ast.FnDef> values,
                  MemoryClassLoader loader) {
        this.module = module;
        this.symbols = symbols;
        this.values = values;
        this.loader = loader;
        this.helpers = new HelperInvoker(module.name(), loader);
        this.neutral = new NeutralForm(symbols);
    }

    /**
     * Whether a value composed elsewhere can be built at this module's boundary.
     *
     * <p>The question a generator cannot answer for itself. Which values a type admits together is the
     * derived decoder's business — an invariant relating two fields refuses a pair that each field
     * would have accepted alone — so the only way to know is to put the value through the decoder that
     * a row's own fixture goes through.
     */
    @FunctionalInterface
    public interface Construction {

        /** Empty where the value builds; why it did not, otherwise. Throws {@link LinkageError} where
         * the runtime is absent, which is not a fact about the value. */
        java.util.Optional<String> refuse(Type type, Ast.Expr fixture);
    }

    /** A way to build values against this module's generated classes, without any rows to run. */
    public static Construction constructing(Ast.Module module, Symbols symbols,
                                            Map<String, byte[]> classes, ClassLoader parent,
                                            Map<String, Ast.FnDef> values) {
        // A reader is the whole of it. There are no rows, so nothing runs on a worker and no budget is
        // read; what a behavior takes and what stands in for what it depends on are not questions about
        // whether a value builds, so this does not ask for the answers to them.
        //
        // One reader per value asked about, because that is what a reading is here as anywhere: a
        // caller holds one of these and asks it about every candidate of every behavior it is
        // measuring, and a reader bound into it once would be a session spanning all of them. It is
        // the loader that is shared, and has to be — it caches the classes it has defined and loaded,
        // and a fake's subclass is generated once.
        MemoryClassLoader loader = new MemoryClassLoader(classes, parent);
        return (type, fixture) -> new FixtureReader(module, symbols, values, loader)
                .refuse(type, fixture);
    }

    /** The helper this reading is inside, for a budget to name when the reading does not finish. */
    String runningHelper() {
        return helpers.running();
    }

    /** One written fixture, decoded against the type of the position it is written in. */
    Object built(Ast.Expr written, Type type) {
        return decode(type, raw(written, type));
    }

    /**
     * A written fixture built into the whole value it states, and the case that value is.
     *
     * <p>What a stand-in installs. A fake row and a {@code with} both have to produce one of these to
     * stand in at all, so both are read this way and neither is read as an assertion.
     */
    record BuiltFixture(TypeName caseName, Object value) {}
    /**
     * The whole value {@code written} states. Throws where it does not build or does not finish —
     * a fixture is one or the other, and what to make of that is the caller's.
     */
    BuiltFixture buildFixture(Ast.Expr written, Type outType) {
        // The one builder a written value goes through, whichever side wrote it: it knows a
        // construction from a literal, a collection, and a value a helper answered with — which the
        // decoder route does not, and a stand-in built the other way stated nothing for a fake whose
        // row applies a helper (the shape of issue #214, on the other side).
        Object value = builtExpected(written, outType);
        TypeName was = caseOfValue(value, outType);
        return new BuiltFixture(was != null ? was : constructedCase(written), value);
    }

    /**
     * Which of the cases {@code outType} holds the built {@code value} is, or null where none of them
     * is what it turned out to be.
     *
     * <p>Matched against the cases the position declares rather than looked up by the name of the
     * class the value arrived in. A class name is not a case name — {@code Int} arrives as a
     * {@code Long} and {@code Date} as a {@code LocalDate}, so a lookup finds nothing and a primitive
     * case reads as no case at all — and resolving one in this module's scope would answer for a case
     * this module happens to declare under the same spelling rather than for the one the value is.
     */
    private TypeName caseOfValue(Object value, Type outType) {
        if (value == null) {
            return null;
        }
        for (TypeName candidate : TypeOps.leafCases(outType, symbols)) {
            if (represents(candidate, value)) {
                return candidate;
            }
        }
        return null;
    }

    /** Whether {@code value} is how {@code candidate} is represented at run time: the class a data
     * case is generated as, and for a primitive case the class its values arrive in. */
    private static boolean represents(TypeName candidate, Object value) {
        String carried = switch (candidate.name()) {
            case "Int" -> "java.lang.Long";
            case "String" -> "java.lang.String";
            case "Bool" -> "java.lang.Boolean";
            case "Decimal" -> "java.math.BigDecimal";
            case "Date" -> "java.time.LocalDate";
            case "DateTime" -> "java.time.LocalDateTime";
            default -> null;
        };
        String is = value.getClass().getName();
        return TypeName.PRIMITIVE.equals(candidate.module())
                ? carried != null && carried.equals(is)
                : is.equals(candidate.qualified());
    }

    /**
     * The case a row asserts and nothing more: a bare name denoting a case — a unit case, or a case
     * written bare — where there is no value under it to compare. Null for anything else, including a
     * name denoting a value, which stands for the value it was defined as.
     *
     * <p>The case's own name, not the spelling: what came out carries the name its type was declared
     * under, so a row spelling that type qualified asserts the same case.
     */
    String caseOnly(Ast.Expr expected) {
        return expected instanceof Ast.Var v && v.denotes() instanceof ValueName.OfType named
                ? named.type().name() : null;
    }

    /** The expected value built the same way as an input, so structural equality compares like with
     * like: a fixture that names a case — written as a construction, or named through a value — decodes
     * through that case's decoder; a literal is its raw value. Throws {@link FixtureException} when the
     * row's expectation cannot be built — the caller reports that as the fixture error it is, rather
     * than comparing against nothing. */
    Object builtExpected(Ast.Expr expected, Type outType) {
        TypeName asserted = constructedCase(expected);
        if (asserted != null) {
            return built(expected, Type.ref(asserted));
        }
        Object answer = helperAnswer(expected, new LinkedHashSet<>());
        if (answer != null) {
            return answer;
        }
        // A collection output has no case name to decode against, so the behavior's declared
        // output type is what says which of `List`/`Set`/`Map` the written list means and what
        // its elements are — the same decision a collection argument's declared type makes.
        if (isCollection(outType)) {
            return built(expected, outType);
        }
        return raw(expected);   // a literal expected value
    }

    /**
     * The value a helper answered with, where a helper answered the whole expectation — written as the
     * application, or named through the values that stand for it. Null where none did.
     *
     * <p>The value itself, not that value read back into the neutral form a fixture is written in. The
     * neutral form is for what encloses a fixture, and nothing encloses this one: reading it back only to
     * decode it again asks a decoder to recover what the helper already built, and which case the answer
     * is — the thing a written construction says and an application does not — is in the value rather
     * than in the text. So a newtype, a record and a case of a union answered by a helper were all
     * compared against their own neutral form, and a row that was right was reported as a mismatch
     * (issue #214).
     */
    private Object helperAnswer(Ast.Expr e, Set<String> followed) {
        return switch (e) {
            case Ast.Apply c when appliedHelper(c) instanceof Ast.FnDef helper -> answered(c, helper);
            case Ast.LetIn let -> helperAnswer(let.body(), followed);
            // a binding holds what it was bound to; a value stands for the body it was defined as.
            // A name that denotes a type is a case, and no helper answered it.
            case Ast.Var v when v.denotes() instanceof ValueName.Local local -> {
                Ast.Expr held = bindings.get(local.id());
                yield held == null ? null : helperAnswer(held, followed);
            }
            case Ast.Var v when v.denotes() instanceof ValueName.Helper -> {
                Ast.Expr body = followed.add(v.name()) ? valueBody(v.name()) : null;
                yield body == null ? null : helperAnswer(body, followed);
            }
            case null, default -> null;
        };
    }

    /** As above, for the rendering of a failure, where a value that cannot be built is shown as
     * written rather than reported a second time. */
    private Object builtExpectedOrNull(Ast.Expr expected, Type outType) {
        try {
            return builtExpected(expected, outType);
        } catch (FixtureException _) {
            return null;
        }
    }

    private static boolean isCollection(Type t) {
        return t instanceof Type.ListOf || t instanceof Type.SetOf || t instanceof Type.MapOf;
    }

    /** The arm an expected names, as it was written — what a row that names no case of the target is
     * told it wrote. Which case it stands for is {@link #constructedCase}. */
    String expectedArm(Ast.Expr expected) {
        if (expected instanceof Ast.Var v) {
            return v.name();
        }
        if (expected instanceof Ast.NewData nd) {
            return nd.typeName().written();
        }
        if (expected instanceof Ast.Apply c && neutral.isNewtype(c.written())) {
            return c.written();
        }
        return null;   // a literal expected (a primitive output)
    }

    /**
     * The case a fixture stands for: the one a construction names, and for a name, the one the value it
     * denotes constructs.
     *
     * <p>Read through the value rather than off the spelling. A value's name is not a case name, and
     * where the position is a union written inline there is no decoder to dispatch on a tag — so the
     * value is the only thing that says which case it is, and reading the name found a type of that
     * spelling or nothing (issue #206).
     */
    TypeName constructedCase(Ast.Expr e) {
        return constructedCase(e, new LinkedHashSet<>());
    }

    /**
     * As above; {@code followed} are the names already followed, so a value defined in terms of itself
     * stops here and is reported as the cycle it is where the fixture is built.
     *
     * <p>The binding a closed body carries is not read here, and does not need to be: a value is
     * substituted where it is named, so the only name closing leaves standing in a fixture is the one a
     * spread holds — a spread cannot hold an expression — and that name is read where the spread is
     * copied. A closed body therefore ends in the construction, whether it was published itself or
     * named by another value that was.
     */
    private TypeName constructedCase(Ast.Expr e, Set<String> followed) {
        return switch (e) {
            case Ast.NewData nd -> nd.typeName().denotes();
            case Ast.Apply c when neutral.isNewtype(c.written()) -> symbols.resolveCase(c.written());
            case Ast.LetIn let -> constructedCase(let.body(), followed);
            case Ast.Var v -> namedCase(v, followed);
            case null, default -> null;
        };
    }

    /** The case a bare name stands for: the type it denotes where it denotes one — a unit case, or a
     * case written bare — and otherwise the case the value or binding it names constructs. */
    private TypeName namedCase(Ast.Var v, Set<String> followed) {
        return switch (v.denotes()) {
            case ValueName.OfType named -> named.type();
            case ValueName.Local local -> {
                Ast.Expr held = bindings.get(local.id());
                yield held == null ? null : constructedCase(held, followed);
            }
            case ValueName.Helper _ -> {
                Ast.Expr body = followed.add(v.name()) ? valueBody(v.name()) : null;
                yield body == null ? null : constructedCase(body, followed);
            }
            case null, default -> null;
        };
    }

    /** The expectation, rendered as the value it stands for: a bare case stays the case name, anything
     * else is its neutral form under the case it constructs ({@code Out { n = 7 }}) — which is what a
     * row naming a value asserts, so that is what the failure shows. */
    String describeExpected(Ast.Expr expected, Type outType) {
        String only = caseOnly(expected);
        if (only != null) {
            return only;   // a bare case asserts only that, so there is no value to show
        }
        TypeName asserted = constructedCase(expected);
        Object built = builtExpectedOrNull(expected, outType);
        if (asserted == null) {
            // Nothing here names a case: a literal, a collection, or a value a helper answered with.
            // What was built is a value, so it is shown the way the result is — which is what puts the
            // two sides of a mismatch in one notation.
            return built == null ? showValue(rawOrNull(expected)) : showAny(built);
        }
        // Render it through the same encoder the actual goes through, so the two sides are written
        // in one notation and can be read against each other; the fixture's own neutral form (which
        // still holds e.g. a LocalDate where the encoder writes its ISO text) is the fallback.
        Object neutral = built == null ? rawOrNull(expected) : encodedOrNull(built, asserted);
        if (neutral == null) {
            neutral = rawOrNull(expected);
        }
        return neutral == null ? asserted.name() : show(asserted.name(), neutral);
    }

    /** What actually came out, in the same notation: the case name plus the value the derived encoder
     * writes, so the two sides of a mismatch can be read against each other. A value with no encoder
     * (or one that fails to encode) falls back to its case name alone. */
    String describeActual(Object result) {
        String name = NeutralForm.simpleName(result);
        if (name.isEmpty()) {
            return String.valueOf(result);
        }
        if (result instanceof Iterable<?> || result instanceof Map<?, ?>) {
            return showAny(result);
        }
        Object encoded = encodedOrNull(result, name);
        if (encoded != null) {
            return show(name, encoded);
        }
        return NeutralForm.isScalar(result) ? showValue(result) : name;
    }

    /** A live value in the notation a fixture is written in, at any depth: a collection element by
     * element, a data as its case name with fields, a scalar as written. Both sides of a collection
     * mismatch go through this, so they can be read against each other — and neither shows the JDK
     * class that happened to carry the collection. */
    private String showAny(Object v) {
        if (v == null || NeutralForm.isScalar(v)) {
            return showValue(v);
        }
        if (v instanceof Map<?, ?> m) {
            List<String> entries = new ArrayList<>();
            for (Map.Entry<?, ?> e : m.entrySet()) {
                entries.add("(" + showAny(e.getKey()) + ", " + showAny(e.getValue()) + ")");
            }
            return entries.isEmpty() ? "[]" : "[ " + String.join(", ", entries) + " ]";
        }
        if (v instanceof Iterable<?> it) {
            List<String> elements = new ArrayList<>();
            for (Object e : it) {
                elements.add(showAny(e));
            }
            return elements.isEmpty() ? "[]" : "[ " + String.join(", ", elements) + " ]";
        }
        String name = NeutralForm.simpleName(v);
        Object encoded = encodedOrNull(v, name);
        return encoded != null ? show(name, encoded) : name;
    }

    /**
     * The generated {@code decoder()} / {@code encoder()} of a type, reached whether or not the type
     * is exposed. {@code exposing} decides what leaves the module, and an {@code example} does not
     * leave it: the fixture is built and the result read back inside the module being compiled, so a
     * module-local type has to be readable here. Its generated class is package-private, which
     * {@link Class#getMethod} cannot reach from this classloader, so the declared method is taken and
     * opened.
     */
    private static Object staticCodec(Class<?> c, String name) throws ReflectiveOperationException {
        java.lang.reflect.Method m = c.getDeclaredMethod(name);
        m.setAccessible(true);
        return m.invoke(null);
    }

    /** {@code result} through its class's derived {@code encoder()}, or null when it has none. */
    private Object encodedOrNull(Object result, String name) {
        TypeName type = symbols.resolve(name);
        return encoded(result, type != null ? type.qualified() : module.name() + "." + name);
    }

    /** As above, for a type already resolved — a fixture says which case it constructs, and that answer
     * names the class whether or not the reader spells the type the way its module does. */
    private Object encodedOrNull(Object result, TypeName type) {
        return encoded(result, type.qualified());
    }

    private Object encoded(Object result, String className) {
        try {
            Class<?> c = loader.loadClass(className);
            Object encoder = staticCodec(c, "encoder");
            return net.unit8.raoh.encode.Encoder.class.getMethod("encode", Object.class)
                    .invoke(encoder, result);
        } catch (ReflectiveOperationException | RuntimeException e) {
            if (souther.compiler.evaluate.EvaluationContext.overspending(e)) {
                throw (RuntimeException) e;   // the evaluation ran out, not this value
            }
            return null;
        }
    }

    /** A case name with its neutral value: a record's fields in braces, a newtype's value in parens,
     * a unit case as the bare name. */
    private String show(String name, Object neutral) {
        if (neutral instanceof Map<?, ?> fields) {
            if (fields.isEmpty()) {
                return name;
            }
            StringBuilder sb = new StringBuilder(name).append(" { ");
            boolean first = true;
            for (Map.Entry<?, ?> e : fields.entrySet()) {
                if (!first) {
                    sb.append(", ");
                }
                first = false;
                sb.append(e.getKey()).append(" = ").append(showValue(e.getValue()));
            }
            return sb.append(" }").toString();
        }
        return name + "(" + showValue(neutral) + ")";
    }

    /** A neutral value in the notation a fixture is written in: a quoted string, a list in brackets,
     * a map as its list of pairs, a date as {@code Date("...")}. */
    private String showValue(Object v) {
        if (v == null) {
            return "None";
        }
        if (v instanceof String s) {
            return "\"" + s + "\"";
        }
        if (v instanceof java.time.LocalDate || v instanceof java.time.LocalDateTime) {
            return (v instanceof java.time.LocalDate ? "Date(\"" : "DateTime(\"") + v + "\")";
        }
        if (v instanceof Map<?, ?> m) {
            List<String> entries = new ArrayList<>();
            for (Map.Entry<?, ?> e : m.entrySet()) {
                entries.add("(" + showValue(e.getKey()) + ", " + showValue(e.getValue()) + ")");
            }
            return entries.isEmpty() ? "[]" : "[ " + String.join(", ", entries) + " ]";
        }
        if (v instanceof Iterable<?> it) {
            List<String> elements = new ArrayList<>();
            for (Object e : it) {
                elements.add(showValue(e));
            }
            return elements.isEmpty() ? "[]" : "[ " + String.join(", ", elements) + " ]";
        }
        return String.valueOf(v);
    }

    private Object rawOrNull(Ast.Expr e) {
        try {
            return raw(e);
        } catch (FixtureException _) {
            return null;
        }
    }

    // --- raw evaluation of a fixture expression -----------------------------------------------

    /** Turns a fixture expression into its neutral (decoder-input) form: a literal to a boxed value,
     * a newtype construction to its inner value, a record construction to a field map. */
    private Object raw(Ast.Expr e) {
        return raw(e, null);
    }

    /**
     * The neutral form of a written fixture value. {@code expected} is the type of the position it is
     * written in, where the caller knows it: a bare case name travels differently depending on the sum
     * it is read as, and only the position says which sum that is. It may be null — a fixture whose
     * position has no declared type — and then the case's own sums decide, which is right whenever
     * they agree.
     */
    private Object raw(Ast.Expr e, Type expected) {
        return switch (e) {
            case Ast.IntLit i -> i.value();
            case Ast.DecimalLit d -> d.value();
            case Ast.StringLit s -> s.value();
            case Ast.BoolLit b -> b.value();
            case Ast.Neg n -> negate(raw(n.operand()));
            case Ast.Binary bin -> fold(bin);
            case Ast.Apply c -> collectionOrNewtype(c, expected);
            case Ast.Var v -> named(v, expected);
            case Ast.NewData nd -> record(nd);
            case Ast.LetIn let -> bound(let, expected);
            case Ast.ListLit l -> {
                Type element = NeutralForm.elementOf(expected);
                List<Object> out = new ArrayList<>();
                for (Ast.Expr el : l.elements()) {
                    out.add(raw(el, element));
                }
                yield out;
            }
            // a `(key, value)` pair: only a `Map` field's entries are written this way, and `shaped`
            // collects them into the map the decoder reads (a tuple is not a data field type itself).
            case Ast.Tuple t -> {
                List<Type> parts = NeutralForm.entryTypes(expected, t.elements().size());
                List<Object> out = new ArrayList<>();
                for (int i = 0; i < t.elements().size(); i++) {
                    out.add(raw(t.elements().get(i), parts == null ? null : parts.get(i)));
                }
                yield out;
            }
            default -> throw new FixtureException("an example fixture must be a literal or a construction");
        };
    }

    /**
     * A bare name in a fixture, read as what it denotes.
     *
     * <p>Which of the four it is was settled where the name was written, so it is not worked out
     * again here: a binding in force is the value it holds, whatever else bears its spelling.
     */
    private Object named(Ast.Var v, Type expected) {
        return switch (v.denotes()) {
            // `None` maps to a null, which the optional decoder reads as the absent optional
            // (spec 8, absent/null -> None), the same as omitting a `T?` field
            case ValueName.Builtin b when b.name().equals("None") -> null;
            case ValueName.OfType named
                    when symbols.get(named.type()) instanceof Ast.UnitData ->
                    unitInput(named.type(), expected);
            case ValueName.Local local -> {
                Ast.Expr held = bindings.get(local.id());
                if (held == null) {
                    throw new FixtureException("`" + v.name()
                            + "` is bound to no value a fixture can name");
                }
                yield expandedValue(local, held, expected);
            }
            case ValueName.Helper helper -> {
                Ast.Expr value = valueBody(v.name());
                if (value == null) {
                    throw new FixtureException("`" + v.name() + "` is not a value a fixture can name");
                }
                yield expandedValue(helper, value, expected);
            }
            // `Map.empty` / `Set.empty`: a library value, not a library call, so there is no method to
            // run and its value is known from the name alone. It is the empty collection, which a row
            // writes `[]` — admitted for the reason `fromList` is (see `collectionOrNewtype`), so a
            // body and a row spell an empty map the one way.
            case ValueName.Stdlib lib when Prelude.isEmptyCollectionValue(lib.qualified()) ->
                    new ArrayList<>();
            case null, default ->
                    throw new FixtureException("`" + v.name() + "` is not a value a fixture can name");
        };
    }

    /** A unit case as a fixture writes it: a unit's decoder ignores the input, so an empty map
     * stands in. */
    private Object unitInput(TypeName caseName, Type expected) {
        {
            String name = caseName.name();
            // A fixture is built in the neutral form the boundary reads, so a case of an enumeration
            // is written the way that sum travels: its name, bare (issue #161). The same unit data may
            // be a case of an enumeration and of a sum that has a field-bearing case, and those travel
            // differently — so the position's own type decides, and the case's sums answer only where
            // the position does not say.
            if (caseName != null && neutral.readsABareName(expected, caseName)) {
                return caseName.name();
            }
            Map<String, Object> unit = new LinkedHashMap<>();
            neutral.tagged(name, unit);   // a unit case of a sum still needs the tag its decoder reads
            return unit;
        }
    }

    /**
     * A name bound while this fixture is being built, holding what it was bound to.
     *
     * <p>A spread holds a name rather than an expression, so a published body that spreads one of its
     * module's values arrives with that value bound ahead of the construction — the shape a spread of a
     * local already has. That binding is what the spread then names, so a fixture reads one the way it
     * reads a value: the position says what type to read it as.
     */
    private final Map<BindingId, Ast.Expr> bindings = new LinkedHashMap<>();

    /** A {@code let} inside a fixture: its name stands for what it was bound to while the body is
     * built, and a binding of the same spelling that was already in force is put back afterwards. */
    private Object bound(Ast.LetIn let, Type expected) {
        BindingId binding = let.binder().id();
        bindings.put(binding, let.value());
        try {
            return raw(let.body(), expected);
        } finally {
            // a binding of its own, so there is nothing of an outer one to put back
            bindings.remove(binding);
        }
    }

    /**
     * What a name stands for: a binding in force, or the body a value — a {@code let} with no parameter
     * list — was defined as. Null where the name is neither.
     *
     * <p>Whether a fixture may name it is not a property of this one body: a value stands for a
     * fixture when it is a literal, a construction, a spread, a {@code fromList} over one, or a name
     * of another such value. So the body is read the same way the row's own text is, and a chain of
     * values holds.
     */
    private Ast.Expr valueBody(String name) {
        for (Ast.FnDef fn : module.fns()) {
            if (fn.name().equals(name) && fn.params().isEmpty()
                    && fn.body() instanceof Ast.FnBody.Written w) {
                return w.expr();
            }
        }
        Ast.FnDef imported = values.get(name);
        return imported != null && imported.params().isEmpty()
                && imported.body() instanceof Ast.FnBody.Written w ? w.expr() : null;
    }

    /**
     * What is being expanded, innermost last — a value that reaches itself has no fixture to be.
     *
     * <p>Held as what each one is rather than as what it is called: two bindings of one spelling are
     * two values, and reading the second while the first is open is not a value reaching itself. The
     * spelling is what the report shows, and decides nothing.
     */
    private final Deque<ValueName> expanding = new ArrayDeque<>();

    private Object expandedValue(ValueName named, Ast.Expr body, Type expected) {
        if (expanding.contains(named)) {
            List<String> cycle = new ArrayList<>();
            expanding.forEach(open -> cycle.add(open.name()));
            cycle.add(named.name());
            throw new FixtureException("`" + named.name() + "` is defined in terms of itself ("
                    + String.join(" -> ", cycle) + ")");
        }
        expanding.addLast(named);
        try {
            return raw(body, expected);
        } finally {
            expanding.removeLast();
        }
    }

    /**
     * {@code Set.fromList([…])} and {@code Map.fromList([…])} are the forms a fixture's own notation
     * stands for — a set is written as its elements and a map as its entry pairs — so the neutral
     * value is the argument's. A value has to be ordinary code, where a list literal is a
     * {@code List} whatever the position declares, so this is what lets one record serve as both a
     * value and a fixture. Anything else applied here is a newtype or nothing.
     *
     * <p>The empty collection is admitted for the same reason, but it is named rather than applied
     * ({@code Map.empty}), so it is read in {@link #named}.
     */
    private Object collectionOrNewtype(Ast.Apply c, Type expected) {
        if ("Set.fromList".equals(c.reaches()) || "Map.fromList".equals(c.reaches())) {
            if (c.args().size() != 1) {
                throw new FixtureException("`" + c.written() + "` takes one argument");
            }
            return raw(c.args().get(0), expected);
        }
        if (appliedHelper(c) instanceof Ast.FnDef helper) {
            return applied(c, helper, expected);
        }
        return newtypeInner(c);
    }

    /** The helper an application applies, or null where the call is not one: a {@code fromList} is the
     * fixture's own notation for a collection and a newtype application is a construction, so neither is
     * a helper however it is spelled. Asked wherever an application has to be told from a construction,
     * so the two readers of a call cannot come to different answers. */
    private Ast.FnDef appliedHelper(Ast.Apply c) {
        if ("Set.fromList".equals(c.reaches()) || "Map.fromList".equals(c.reaches())
                || neutral.isNewtype(c.written())) {
            return null;
        }
        return helperDef(c.written());
    }

    /**
     * The helper a fixture may apply under {@code name}, or null where the name is not one: a
     * definition written with a parameter list, read from the table that keys every helper this module
     * reaches — its own, the ones its imports publish, and the prelude's — as the emitted method is
     * keyed. The types come from there rather than from the written module because that table is
     * settled (ADR-0066), and an argument is decoded against the parameter's settled type.
     */
    private Ast.FnDef helperDef(String name) {
        Ast.FnDef helper = values.get(name);
        return helper != null && !helper.params().isEmpty() ? helper : null;
    }

    /** Whether {@code name} is a function this example cannot run: nothing emitted a method for it.
     * A helper that has one is applied; the ones that never do are the standard library's intrinsics
     * and a helper whose body produces a function, and both read as this. */
    private boolean noMethod(String name) {
        if (Prelude.isLibraryFunction(name)) {
            return true;   // a standard-library function: an intrinsic, or one nothing emitted here
        }
        for (Ast.FnDef fn : module.fns()) {
            if (fn.name().equals(name) && !fn.params().isEmpty()) {
                return true;
            }
        }
        return false;
    }

    /**
     * A helper applied inside a fixture: it is run, and the value it returns is re-materialised into the
     * neutral form a fixture is written in — so what encloses the call goes on being built the one way,
     * a field of a record and an element of a list alike. An application that encloses nothing is
     * {@link #helperAnswer}: there the value itself is what the row asserts.
     */
    private Object applied(Ast.Apply c, Ast.FnDef helper, Type expected) {
        return neutral.of(answered(c, helper), expected, c.written());
    }

    /** The value a helper answers with, run as the method its module emits. Its arguments are fixtures
     * built against its parameter types, so an argument breaking one of those types' invariants is
     * reported as the fixture it is. */
    private Object answered(Ast.Apply c, Ast.FnDef helper) {
        if (c.args().size() != helper.params().size()) {
            throw new FixtureException("`" + c.written() + "` takes " + helper.params().size()
                    + " argument(s) but is called with " + c.args().size());
        }
        Object[] args = new Object[helper.params().size()];
        for (int i = 0; i < args.length; i++) {
            Ast.FnParam p = helper.params().get(i);
            if (p.type() == null) {
                throw new FixtureException("`" + c.written() + "` parameter `" + p.name()
                        + "` has no type a fixture can be built against");
            }
            Type paramType = TypeOps.resolveParamType(p.type(), symbols);
            // A parameter whose element each call decides has no one type here. A call settles it
            // from the argument it is given; a fixture is built before there is a call to settle it,
            // so the order is what refuses this rather than the type being unsupported.
            if (Type.mentions(paramType, t -> t instanceof Type.Var)) {
                throw new FixtureException("`" + c.written() + "` parameter `" + p.name() + "` is "
                        + Type.show(paramType) + "; what it holds is decided by each call, and a"
                        + " fixture is built before a call can decide it");
            }
            args[i] = built(c.args().get(i), paramType);
        }
        return helpers.invoke(c.written(), args);
    }

    private Object newtypeInner(Ast.Apply c) {
        if ("Date".equals(c.reaches()) || "DateTime".equals(c.reaches())) {
            // a written date: the decoders take the parsed temporal, not its text (a Date field's
            // neutral form is a LocalDate), so the fixture hands over the same value the checker read
            if (c.args().size() != 1 || !(c.args().get(0) instanceof Ast.StringLit lit)) {
                throw new FixtureException("`" + c.written() + "` takes one written string");
            }
            return CallElaborator.parseTemporal(c.written(), lit.value(), c.pos());
        }
        if (!neutral.isNewtype(c.written())) {
            if (noMethod(c.written())) {
                // A function this module cannot run: an intrinsic implemented in Java, or a helper
                // whose body produces a function. Said as that, so the rule that a fixture may apply a
                // helper does not appear to have exceptions nothing explains (ADR-0077).
                throw new FixtureException("`" + c.written() + "` cannot be called from an example fixture:"
                        + " it has no executable helper method");
            }
            throw new FixtureException("`" + c.written() + "` is not a newtype; a fixture cannot call it");
        }
        if (c.args().size() != 1) {
            throw new FixtureException("`" + c.written() + "` takes one argument");
        }
        // a newtype over a temporal (`data 貸出日 = Date`) wraps the parsed value, so its written
        // string is read here as it would be for a bare `Date("...")`
        String base = neutral.newtypeBase(c.written());
        if (("Date".equals(base) || "DateTime".equals(base))
                && c.args().get(0) instanceof Ast.StringLit lit) {
            return CallElaborator.parseTemporal(base, lit.value(), c.pos());
        }
        // the argument is shaped against what the newtype wraps, the same way a record fixture
        // shapes a field's value: a `Map` newtype's entry pairs become a map, a `Set` newtype's
        // written list stays a list for its decoder to dedupe
        return neutral.adjacentlyTagged(c.written(),
                neutral.shaped(raw(c.args().get(0), neutral.shapeOf(neutral.newtypeBaseType(c.written()))),
                        neutral.shapeOf(neutral.newtypeBaseType(c.written()))));
    }

    private Object record(Ast.NewData nd) {
        // `金額(500)` is the record literal `金額 { value = 500 }` written in call form (ADR-0032), and
        // a value's body reaches here already written the second way. Either spelling is the newtype's
        // own neutral form — its inner value — not a field map.
        TypeName built = nd.typeName().denotes();
        if (neutral.isNewtype(built) && nd.spreads().isEmpty() && nd.inits().size() == 1
                && nd.inits().get(0).name().equals("value")) {
            return neutral.adjacentlyTagged(nd.typeName().written(),
                    neutral.shaped(raw(nd.inits().get(0).value(), neutral.shapeOf(neutral.newtypeBaseType(built))),
                            neutral.shapeOf(neutral.newtypeBaseType(built))));
        }
        Map<String, Ast.TypeRef> declared = neutral.fieldTypes(nd.typeName().denotes());
        Map<String, Object> map = new LinkedHashMap<>();
        // `...base` copies the fields of a value, and the fields written after it replace what it
        // brought.
        for (Ast.Var ref : nd.spreads()) {
            // A spread names a value in force, so what it copies is what that name denotes: a binding
            // holds what it was bound to, and a definition stands for its body. A definition is
            // reached by the name this row spells it with — a definition of this module by its own
            // name, one another module published by that module's name and its own. `bare()` is the
            // name it was *declared* under, which is not that key for an imported value (issue #212).
            String spread = ref.name();
            Ast.Expr value = ref.denotes() instanceof ValueName.Local local
                    ? bindings.get(local.id()) : valueBody(spread);
            if (value == null) {
                throw new FixtureException("`" + spread
                        + "` is not a value a fixture can spread");
            }
            Object copied = expandedValue(ref.denotes(), value,
                    Type.ref(nd.typeName().denotes()));
            if (!(copied instanceof Map<?, ?> fields)) {
                throw new FixtureException("`" + spread + "` is not a record, so it has no fields to"
                        + " spread");
            }
            for (Map.Entry<?, ?> f : fields.entrySet()) {
                String field = String.valueOf(f.getKey());
                // A spread copies fields, and only the ones this construction has — which is what the
                // language copies. The discriminator the spread source's own sum's decoder reads is not
                // one of them: it says which case that value is, and this construction says which case
                // it builds (below). Copying it left the source's case in place of it, and where the
                // position is a union that is the case the behavior saw (issue #206).
                if (declared.containsKey(field)) {
                    map.put(field, f.getValue());
                }
            }
        }
        for (Ast.FieldInit fi : nd.inits()) {
            Object v = neutral.shaped(raw(fi.value(), neutral.shapeOf(declared.get(fi.name()))),
                    neutral.shapeOf(declared.get(fi.name())));
            // `None` on a `T?` field yields a null; leave the key out so the optional decoder reads
            // it as absent (spec 8, absent -> None), the same neutral form as omitting the field.
            // A spread already wrote the field, so leaving the key out means taking it back out —
            // not writing nothing, which would leave what the spread copied standing.
            if (v == null) {
                map.remove(fi.name());
                continue;
            }
            map.put(fi.name(), v);
        }
        neutral.tagged(nd.typeName().denotes(), map);
        return map;
    }

    private static Object negate(Object v) {
        if (v instanceof Long l) {
            return -l;
        }
        if (v instanceof BigDecimal d) {
            return d.negate();
        }
        throw new FixtureException("only a number can be negated in a fixture");
    }

    private Object fold(Ast.Binary b) {
        Object l = raw(b.left());
        Object r = raw(b.right());
        if (l instanceof Long x && r instanceof Long y) {
            return switch (b.op()) {
                case ADD -> x + y;
                case SUB -> x - y;
                case MUL -> x * y;
                default -> throw new FixtureException("unsupported arithmetic in a fixture");
            };
        }
        if (l instanceof BigDecimal x && r instanceof BigDecimal y) {
            return switch (b.op()) {
                case ADD -> x.add(y);
                case SUB -> x.subtract(y);
                case MUL -> x.multiply(y);
                default -> throw new FixtureException("unsupported arithmetic in a fixture");
            };
        }
        throw new FixtureException("a fixture can only combine numbers of the same kind");
    }

    // --- decode a raw value into the parameter/expected type ----------------------------------

    private Object decode(Type type, Object rawValue) {
        Object raw = neutral.shaped(rawValue, type);
        Decoder<Object, ?> decoder = decoderFor(type);
        Result<?> result;
        try {
            result = decoder.decode(raw, net.unit8.raoh.Path.ROOT);
        } catch (RuntimeException e) {
            if (souther.compiler.evaluate.EvaluationContext.overspending(e)) {
                throw e;   // the evaluation ran out, not this fixture failing to fit
            }
            // The decoder is generated for the declared type and casts on the way in, so a fixture of
            // another shape — a string where the parameter is a product, a number where it is a
            // string-backed newtype — fails inside it rather than returning an Err. That is the
            // fixture's problem, and it reads as one (E1903) instead of aborting the compile.
            throw new FixtureException("a " + shapeOf(raw) + " does not fit " + Type.show(type));
        }
        if (result instanceof Ok<?> ok) {
            return ok.value();
        }
        // Name where each failure landed. A decoder reports at a path, and a fixture that breaks the
        // same rule twice — two keys of a newtype-keyed map, two elements of a list — otherwise reads
        // as one message repeated, with nothing to say which value it is about.
        String detail = ((Err<?>) result).issues().asList().stream()
                .map(issue -> {
                    String at = String.join(".", issue.path().segments());
                    return at.isEmpty() ? issue.message() : at + ": " + issue.message();
                })
                .collect(java.util.stream.Collectors.joining("; "));
        throw new FixtureException(detail);
    }

    /** What a fixture value looks like from the decode boundary, for the message above: the raw kinds
     *  a fixture can produce, named as the author wrote them rather than by their JVM class. */
    private static String shapeOf(Object raw) {
        return switch (raw) {
            case null -> "missing value";
            case String _ -> "string";
            case Long _, Integer _ -> "number";
            case java.math.BigDecimal _ -> "decimal";
            case Boolean _ -> "boolean";
            case java.util.Map<?, ?> _ -> "record";
            case java.util.List<?> _ -> "list";
            default -> raw.getClass().getSimpleName();
        };
    }

    @SuppressWarnings("unchecked")
    private Decoder<Object, ?> decoderFor(Type type) {
        if (type instanceof Type.Prim prim) {
            return switch (prim) {
                case STRING -> ObjectDecoders.string();
                case INT -> ObjectDecoders.long_();
                case BOOL -> ObjectDecoders.bool();
                case DECIMAL -> ObjectDecoders.decimal();
                case DATE -> ObjectDecoders.date();
                case DATETIME -> ObjectDecoders.dateTime();
                case RAW -> throw new FixtureException("the Raw type cannot be an example input");
            };
        }
        if (type instanceof Type.Ref ref) {
            // An imported type's decoder lives in its declaring module's package, not this one's.
            try {
                Class<?> c = loader.loadClass(ref.name().qualified());
                return (Decoder<Object, ?>) staticCodec(c, "decoder");
            } catch (ReflectiveOperationException _) {
                throw new FixtureException("no decoder for `" + ref.name().name() + "`");
            }
        }
        // A collection is decoded the way a data's collection field is, built from the same pieces the
        // derived decoder is (spec 10.2): a list over its element decoder, a set as a list
        // deduplicated, a map over its value decoder with the keys remapped through the key type.
        // Without this a collection could only reach an example inside a data, so a behavior taking
        // one had to be given a wrapper that exists for no other reason (issue #97).
        if (type instanceof Type.ListOf list) {
            return ObjectDecoders.list(decoderFor(list.element()));
        }
        if (type instanceof Type.SetOf set) {
            return ObjectDecoders.list(decoderFor(set.element()))
                    .map(elements -> Sets.fromList(new ArrayList<Object>(elements)));
        }
        if (type instanceof Type.MapOf map) {
            Decoder<Object, ?> values = ObjectDecoders.map(decoderFor(map.value()));
            return map.key() instanceof Type.Ref key ? rekeyed(values, key) : values;
        }
        throw new FixtureException("`" + Type.show(type) + "` is not supported as an example value yet");
    }

    /**
     * A map whose keys are a newtype ({@code Map<商品ID, Int>}, ADR-0040): the values decode first, as
     * the derived decoder does, then each key is built through its own type — so the key's invariant
     * runs and a fixture that breaks it is reported instead of reaching the behavior as a bare string.
     * Every key is tried and its failures merged, as the derived decoder's rekey helper does, so a
     * fixture with two bad keys names both rather than stopping at the first.
     */
    private Decoder<Object, ?> rekeyed(Decoder<Object, ?> values, Type.Ref key) {
        Decoder<Object, ?> keyDecoder = decoderFor(key);
        return values.flatMapWithPath((decoded, path) -> {
            Map<Object, Object> out = new LinkedHashMap<>();
            Issues issues = Issues.EMPTY;
            for (Map.Entry<?, ?> entry : ((Map<?, ?>) decoded).entrySet()) {
                Result<?> k = keyDecoder.decode(entry.getKey(), path.append(String.valueOf(entry.getKey())));
                switch (k) {
                    case Ok<?>(var decodedKey) -> out.put(decodedKey, entry.getValue());
                    case Err<?>(var found) -> issues = issues.merge(found);
                }
            }
            return issues.isEmpty() ? Result.ok(out) : Result.err(issues);
        });
    }

    /** One decoded input, in the form the compiler owns. Never throws: a value that cannot be read is
     * an unreadable value, and a row that carries one still carries everything else. */
    ObservedValue observed(Object decoded) {
        try {
            return ObservedValues.of(decoded, symbols, neutral, Limits.DEFAULT);
        } catch (RuntimeException | LinkageError e) {
            if (souther.compiler.evaluate.EvaluationContext.overspending(e)) {
                throw (RuntimeException) e;   // the evaluation ran out, not this value being unreadable
            }
            return new ObservedValue.Unknown(e.getClass().getSimpleName());
        }
    }

    java.util.Optional<String> refuse(Type type, Ast.Expr fixture) {
        try {
            built(fixture, type);
            return java.util.Optional.empty();
        } catch (FixtureException e) {
            return java.util.Optional.of(e.getMessage());
        } catch (RuntimeException e) {
            if (souther.compiler.evaluate.EvaluationContext.overspending(e)) {
                throw e;   // the evaluation ran out; whether the fixture is refused is still unread
            }
            return java.util.Optional.of(String.valueOf(e.getMessage()));
        }
    }
}
