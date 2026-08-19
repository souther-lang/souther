package souther.compiler.examples;

import souther.compiler.ast.Hir;
import souther.compiler.check.Symbols;
import souther.compiler.observe.Limits;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.TypeSymbol;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Reads a decoded value into the form the compiler owns ({@link ObservedValue}).
 *
 * <p>Here rather than in {@code souther.compiler.observe} because the rules for what a data's fields
 * are — following the {@code ...includes} it composes in, and a newtype's single {@code value} — are
 * {@link NeutralForm}'s, and a second statement of them would drift from the first. This walk is the
 * one {@link NeutralForm#of} makes in the other direction: that one produces the form a decoder reads,
 * this one produces the form a measure reads.
 *
 * <p>The walk never fails. A value it cannot read becomes {@link ObservedValue.Unknown}, which says
 * why, and an observation {@link Limits} stopped becomes {@link ObservedValue.Truncated}, which says
 * only that — a measure that cannot classify a row has to say so rather than count the row as
 * covering nothing. The second is not the same as a large value: the node budget is one for the
 * whole walk, so a small value observed after a large sibling is truncated as well.
 */
final class ObservedValues {

    private final Symbols symbols;
    private final NeutralForm neutral;
    private final Limits limits;
    /** How many nodes the whole observation may still hold. One budget for the walk, not per subtree. */
    private int budget;

    private ObservedValues(Symbols symbols, NeutralForm neutral, Limits limits) {
        this.symbols = symbols;
        this.neutral = neutral;
        this.limits = limits;
        this.budget = limits.maxNodes();
    }

    /** Observes one decoded value under {@code limits}. */
    static ObservedValue of(Object live, Symbols symbols, NeutralForm neutral, Limits limits) {
        return new ObservedValues(symbols, neutral, limits).walk(live, 0);
    }

    private ObservedValue walk(Object live, int depth) {
        if (budget-- <= 0) {
            return new ObservedValue.Truncated();
        }
        if (depth > limits.maxDepth()) {
            return new ObservedValue.Truncated();
        }
        return switch (live) {
            case null -> new ObservedValue.Unknown("a null reached the observer");
            case Boolean b -> new ObservedValue.Bool(b);
            case Long l -> new ObservedValue.Integer(l);
            case java.lang.Integer i -> new ObservedValue.Integer(i.longValue());
            case BigDecimal d -> new ObservedValue.Decimal(d);
            case String s -> text(s);
            case java.time.LocalDate d -> new ObservedValue.Temporal(d.toString());
            // Spelled to the second by whatever writes the value everywhere else. `toString` drops
            // the seconds at zero on both of these, so an observation carried `16:00` where a line
            // drawn at the same value is named `16:00:00` — one value in two spellings, and the
            // report holding both is the one a reader compares them in.
            case java.time.LocalTime t ->
                    new ObservedValue.Temporal(souther.compiler.numeric.Times.written(t));
            case java.time.LocalDateTime d ->
                    new ObservedValue.Temporal(souther.compiler.numeric.DateTimes.written(d));
            case java.time.Instant i -> new ObservedValue.Temporal(i.toString());
            case Map<?, ?> m -> mapping(m, depth);
            case Iterable<?> it -> sequence(it, depth);
            default -> constructed(live, depth);
        };
    }

    private ObservedValue text(String s) {
        return s.length() <= limits.maxText()
                ? new ObservedValue.Text(s)
                : new ObservedValue.Truncated();
    }

    /** A collection past the element limit is dropped whole rather than kept as a prefix. A prefix
     * is not the value that was written, and returned as a {@link ObservedValue.Sequence} it would
     * be the same thing as a complete observation of a shorter collection — nothing about the two
     * would differ. {@link ObservedValue.Truncated} keeps the one fact that stays true: the
     * observation stopped. */
    private ObservedValue sequence(Iterable<?> it, int depth) {
        List<ObservedValue> out = new ArrayList<>();
        for (Object e : it) {
            if (out.size() >= limits.maxElements()) {
                return new ObservedValue.Truncated();
            }
            out.add(walk(e, depth + 1));
        }
        return new ObservedValue.Sequence(out);
    }

    private ObservedValue mapping(Map<?, ?> m, int depth) {
        if (m.size() > limits.maxElements()) {
            return new ObservedValue.Truncated();
        }
        List<ObservedValue.Entry> out = new ArrayList<>(m.size());
        for (Map.Entry<?, ?> e : m.entrySet()) {
            out.add(new ObservedValue.Entry(walk(e.getKey(), depth + 1), walk(e.getValue(), depth + 1)));
        }
        return new ObservedValue.Mapping(out);
    }

    private ObservedValue constructed(Object live, int depth) {
        String name = NeutralForm.simpleName(live);
        // An optional is its payload where it holds one, and `Absent` where it does not — which is what
        // a fixture writes by leaving the field out (spec §optional).
        if (name.equals("Option$None")) {
            return new ObservedValue.Absent();
        }
        if (name.equals("Option$Some")) {
            Object inner = read(live, "value");
            return inner == FAILED
                    ? new ObservedValue.Unknown("an optional's value could not be read")
                    : walk(inner, depth);
        }
        TypeSymbol type = neutral.typeOf(live);
        if (type == null) {
            return new ObservedValue.Unknown("`" + name + "` is not a type this module can name");
        }
        if (!(symbols.declarations().declaration(type.key()) instanceof Hir.Data data)) {
            return new ObservedValue.Unit(type);   // a case that carries nothing
        }
        Map<String, ObservedValue> fields = ObservedValue.fields();
        if (data.newtype()) {
            fields.put("value", field(live, "value", depth));
            return new ObservedValue.Constructed(type, fields);
        }
        for (String each : neutral.fieldTypes(type).keySet()) {
            fields.put(each, field(live, each, depth));
        }
        return new ObservedValue.Constructed(type, fields);
    }

    private ObservedValue field(Object live, String name, int depth) {
        Object value = read(live, name);
        return value == FAILED
                ? new ObservedValue.Unknown("`" + name + "` could not be read from `"
                        + NeutralForm.simpleName(live) + "`")
                : walk(value, depth + 1);
    }

    /** A sentinel for "the accessor did not answer", so that a field holding {@code null} and a field
     * that could not be read stay different things. */
    private static final Object FAILED = new Object();

    /** One field, through the accessor every data has (ADR-0065). The class may be package-private, so
     * the declared method is taken and opened, the way a codec is. */
    static Object readOrNull(Object live, String name) {
        Object value = read(live, name);
        return value == FAILED ? null : value;
    }

    private static Object read(Object live, String name) {
        try {
            java.lang.reflect.Method accessor = live.getClass().getDeclaredMethod(name);
            accessor.setAccessible(true);
            return accessor.invoke(live);
        } catch (ReflectiveOperationException | RuntimeException _) {
            return FAILED;
        }
    }

}
