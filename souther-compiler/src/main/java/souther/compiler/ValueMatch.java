package souther.compiler;

import souther.compiler.ast.Ast;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Whether what a row asserted and what a behavior answered are the same value, and where they are not.
 *
 * <p>Both sides are structured values ({@link ObservedValue}), and neither is read as the other. What
 * a row asserted carries the names the row wrote; what came back carries the names its classes were
 * declared under. Two values differ when their names differ as much as when their contents do, and
 * saying which is the whole reason this is not {@code Values.equal} over the run-time objects: those
 * are compared as values of one type, and the question here is whether they are of one type at all.
 *
 * <p>{@code position} is semantic context and never a conversion target. It answers one question the
 * values cannot answer about themselves — an {@link ObservedValue.Sequence} is a {@code List} and a
 * {@code Set} alike, and which one it is decides whether order is part of being the same value. It
 * never supplies a name: the position a child is read at comes from the type its <em>parent value</em>
 * declared, so a field of a {@code Receipt} is read at what {@code Receipt} declares and not at what
 * the surrounding expectation happened to be written for.
 */
final class ValueMatch {

    /** Where the two differ, the path it is at, and which of the two questions it fails. */
    record Mismatch(String path, Reason reason, ObservedValue asserted, ObservedValue observed) {}

    /**
     * Why two values are not the same value.
     *
     * <p>{@link #TYPE} and {@link #VALUE} are the distinction this class exists for: a row writing
     * {@code 1} where an {@code AmountN} comes out disagrees about what type stands there, which is
     * not the same disagreement as writing the wrong number.
     */
    enum Reason {
        /** The two are of different types — a name against another name, or against no name at all. */
        TYPE,
        /** One type, different contents. */
        VALUE,
        /** The same kind of container, holding a different set of positions. */
        SHAPE,
        /** One is absent where the other is present. */
        ABSENCE,
        /** One side could not be read back, so nothing about it can be compared. */
        UNREADABLE
    }

    private final NeutralForm neutral;
    private final ValueRendering rendering;

    ValueMatch(NeutralForm neutral, ValueRendering rendering) {
        this.neutral = neutral;
        this.rendering = rendering;
    }

    /** Null where the two are the same value. */
    Mismatch compare(ObservedValue asserted, ObservedValue observed, Type position) {
        return at("$", asserted, observed, position);
    }

    private Mismatch at(String path, ObservedValue a, ObservedValue o, Type position) {
        if (a.unread() != null || o.unread() != null) {
            return new Mismatch(path, Reason.UNREADABLE, a, o);
        }
        if (a instanceof ObservedValue.Absent || o instanceof ObservedValue.Absent) {
            return a instanceof ObservedValue.Absent && o instanceof ObservedValue.Absent
                    ? null : new Mismatch(path, Reason.ABSENCE, a, o);
        }
        return switch (a) {
            case ObservedValue.Bool x -> o instanceof ObservedValue.Bool y
                    ? same(path, x.value() == y.value(), a, o) : new Mismatch(path, Reason.TYPE, a, o);
            case ObservedValue.Integer x -> o instanceof ObservedValue.Integer y
                    ? same(path, x.value() == y.value(), a, o) : new Mismatch(path, Reason.TYPE, a, o);
            // A decimal is the amount it stands for, so two that differ only in scale are one amount
            // — the rule `Values.equal` states for the run-time values.
            case ObservedValue.Decimal x -> o instanceof ObservedValue.Decimal y
                    ? same(path, x.value().compareTo(y.value()) == 0, a, o)
                    : new Mismatch(path, Reason.TYPE, a, o);
            case ObservedValue.Text x -> o instanceof ObservedValue.Text y
                    ? same(path, x.value().equals(y.value()), a, o) : new Mismatch(path, Reason.TYPE, a, o);
            // Kept apart from text, so a row writing a date as a string is told the two are of
            // different types rather than being read as one.
            case ObservedValue.Temporal x -> o instanceof ObservedValue.Temporal y
                    ? same(path, x.iso().equals(y.iso()), a, o) : new Mismatch(path, Reason.TYPE, a, o);
            case ObservedValue.Unit x -> o instanceof ObservedValue.Unit y && x.type().equals(y.type())
                    ? null : new Mismatch(path, Reason.TYPE, a, o);
            case ObservedValue.Constructed x -> constructed(path, x, o);
            case ObservedValue.Sequence x -> o instanceof ObservedValue.Sequence y
                    ? sequence(path, x, y, position) : new Mismatch(path, Reason.TYPE, a, o);
            case ObservedValue.Mapping x -> o instanceof ObservedValue.Mapping y
                    ? mapping(path, x, y, position) : new Mismatch(path, Reason.TYPE, a, o);
            case ObservedValue.Absent _, ObservedValue.Unknown _, ObservedValue.Truncated _ ->
                    new Mismatch(path, Reason.UNREADABLE, a, o);
        };
    }

    private static Mismatch same(String path, boolean equal, ObservedValue a, ObservedValue o) {
        return equal ? null : new Mismatch(path, Reason.VALUE, a, o);
    }

    /**
     * Two constructions. The names first, because a value is of its type before it is anything else:
     * a {@code Receipt} whose {@code total} the row wrote as a number and one whose {@code total} is
     * an {@code AmountN} are not one value written two ways.
     */
    private Mismatch constructed(String path, ObservedValue.Constructed a, ObservedValue o) {
        if (!(o instanceof ObservedValue.Constructed b)) {
            return new Mismatch(path, Reason.TYPE, a, o);
        }
        if (!a.type().equals(b.type())) {
            return new Mismatch(path, Reason.TYPE, a, o);
        }
        Set<String> names = new LinkedHashSet<>(a.fields().keySet());
        names.addAll(b.fields().keySet());
        for (String name : names) {
            ObservedValue x = a.field(name);
            ObservedValue y = b.field(name);
            if (x == null || y == null) {
                return new Mismatch(path + "." + name, Reason.SHAPE, a, o);
            }
            // The child's position comes from what this value's own type declares that field to be,
            // so nothing outside the value supplies a name for what stands under it.
            Mismatch under = at(path + "." + name, x, y, fieldType(a.type(), name));
            if (under != null) {
                return under;
            }
        }
        return null;
    }

    /** What {@code type} declares {@code field} to be, or null where nothing says. A newtype's single
     *  {@code value} is read the same way, since that is the field it is written with. */
    private Type fieldType(TypeName type, String field) {
        Map<String, Ast.TypeRef> declared = neutral.fieldTypes(type);
        return declared.containsKey(field) ? neutral.shapeOf(declared.get(field)) : null;
    }

    /**
     * Two sequences, ordered or not as the position says. A {@code List} is its elements in order and
     * a {@code Set} is its elements, and the values cannot tell the two apart — a sequence is how each
     * of them is read back.
     */
    private Mismatch sequence(String path, ObservedValue.Sequence a, ObservedValue.Sequence b,
                              Type position) {
        Type open = NeutralForm.open(position);
        Type element = switch (open) {
            case Type.ListOf l -> l.element();
            case Type.SetOf s -> s.element();
            case null, default -> null;
        };
        if (a.elements().size() != b.elements().size()) {
            return new Mismatch(path, Reason.SHAPE, a, b);
        }
        if (open instanceof Type.SetOf) {
            return unordered(path, a.elements(), b.elements(), element, a, b);
        }
        for (int i = 0; i < a.elements().size(); i++) {
            Mismatch under = at(path + "[" + i + "]", a.elements().get(i), b.elements().get(i), element);
            if (under != null) {
                return under;
            }
        }
        return null;
    }

    /** A set: each element of one stands for one of the other, and which one is not part of the value. */
    private Mismatch unordered(String path, List<ObservedValue> xs, List<ObservedValue> ys, Type element,
                               ObservedValue a, ObservedValue o) {
        List<ObservedValue> left = new ArrayList<>(ys);
        for (ObservedValue x : xs) {
            boolean found = false;
            for (int i = 0; i < left.size(); i++) {
                if (at(path, x, left.get(i), element) == null) {
                    left.remove(i);
                    found = true;
                    break;
                }
            }
            if (!found) {
                return new Mismatch(path, Reason.SHAPE, a, o);
            }
        }
        return null;
    }

    /**
     * Two maps, matched by key rather than looked up by one. A key is the same key under the same rule
     * everything else here is compared by, which a hash lookup would answer with Java's equality — and
     * a key written under a name is not the base it wraps.
     */
    private Mismatch mapping(String path, ObservedValue.Mapping a, ObservedValue.Mapping b, Type position) {
        Type open = NeutralForm.open(position);
        Type key = open instanceof Type.MapOf m ? m.key() : null;
        Type value = open instanceof Type.MapOf m ? m.value() : null;
        if (a.entries().size() != b.entries().size()) {
            return new Mismatch(path, Reason.SHAPE, a, b);
        }
        List<ObservedValue.Entry> left = new ArrayList<>(b.entries());
        for (ObservedValue.Entry entry : a.entries()) {
            int found = -1;
            for (int i = 0; i < left.size(); i++) {
                if (at(path, entry.key(), left.get(i).key(), key) == null) {
                    found = i;
                    break;
                }
            }
            if (found < 0) {
                return new Mismatch(path, Reason.SHAPE, a, b);
            }
            ObservedValue.Entry match = left.remove(found);
            Mismatch under = at(path + "[" + rendering.show(entry.key()) + "]", entry.value(),
                    match.value(), value);
            if (under != null) {
                return under;
            }
        }
        return null;
    }
}
