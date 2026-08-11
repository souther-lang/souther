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
 * Whether what a row stated and what a behavior answered are the same value, and where they are not.
 *
 * <p>The two sides are not one kind of thing and are not read as one. {@link Asserted} is what a row
 * wrote, carrying the names and the forms the row wrote them under; {@link ObservedValue} is what a
 * value turned out to be. Two values differ when their types differ as much as when their contents
 * do, and saying which is the whole reason this is not {@code Values.equal} over the run-time
 * objects: those are compared as values of one type, and the question here is whether they are of one
 * type at all.
 *
 * <p>{@code position} is what the behavior's declaration says stands here, so it says what the
 * <em>answer</em> is: an {@link ObservedValue.Sequence} is a {@code List} and a {@code Set} alike, and
 * which one it is comes from the type that produced it. It says nothing about what the row wrote. A
 * row that wrote which collection it meant is held to that, and one that did not — {@code [ 1 ]} is
 * how both are written — is read at what the answer is, since there is nothing else for it to be.
 */
final class ValueMatch {

    /**
     * Where the two differ, the path it is at, and which of the two questions it fails.
     *
     * <p>{@code position} is what the behavior declares at that path. It is carried rather than left
     * to be worked out again, because what a value is there was already decided here: an observation
     * does not say whether its sequence is a list or a set, and a renderer asking that question a
     * second time would be a second reading of it, free to answer differently from the comparison
     * that reported the mismatch.
     */
    record Mismatch(String path, Reason reason, Asserted asserted, ObservedValue observed,
                    Type position) {}

    /**
     * Why two values are not the same value.
     *
     * <p>{@link #TYPE} and {@link #VALUE} are the distinction this class exists for: a row writing
     * {@code 1} where an {@code AmountN} comes out disagrees about what type stands there, which is
     * not the same disagreement as writing the wrong number.
     */
    enum Reason {
        /** The two are of different types — a name against another name, a list against a set, or
         *  against no name at all. */
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
    Mismatch compare(Asserted asserted, ObservedValue observed, Type position) {
        return at("$", asserted, observed, position);
    }

    private Mismatch at(String path, Asserted a, ObservedValue o, Type position) {
        if (o.unread() != null) {
            return new Mismatch(path, Reason.UNREADABLE, a, o, position);
        }
        return switch (a) {
            case Asserted.Value(ObservedValue v) -> leaf(path, a, v, o, position);
            case Asserted.Built built -> constructed(path, a, built, o, position);
            case Asserted.Elements elements -> sequence(path, a, elements, o, position);
            case Asserted.Entries entries -> mapping(path, a, entries, o, position);
        };
    }

    /** A value with no parts against one. Absence is neither a type nor a value of one: a position
     *  holds nothing or holds something, and that is its own answer. */
    private Mismatch leaf(String path, Asserted a, ObservedValue v, ObservedValue o, Type position) {
        if (v.unread() != null) {
            return new Mismatch(path, Reason.UNREADABLE, a, o, position);
        }
        if (v instanceof ObservedValue.Absent || o instanceof ObservedValue.Absent) {
            return v instanceof ObservedValue.Absent && o instanceof ObservedValue.Absent
                    ? null : new Mismatch(path, Reason.ABSENCE, a, o, position);
        }
        // Of one type before anything else, and which type a written value with no parts is has one
        // answer for every reader of it. A row writing `1` where a `Decimal` came out wrote an `Int`
        // — the difference is written in the language, and reading a whole number as an amount is
        // what a boundary does and not what a row did.
        Type.Prim stated = ValueRendering.primitiveOf(v);
        Type.Prim answered = ValueRendering.primitiveOf(o);
        if (stated == null || stated != answered) {
            return v instanceof ObservedValue.Unit x && o instanceof ObservedValue.Unit y
                    && x.type().equals(y.type())
                    ? null : new Mismatch(path, Reason.TYPE, a, o, position);
        }
        return switch (v) {
            case ObservedValue.Bool x ->
                    same(path, x.value() == ((ObservedValue.Bool) o).value(), a, o, position);
            case ObservedValue.Integer x ->
                    same(path, x.value() == ((ObservedValue.Integer) o).value(), a, o, position);
            // A decimal is the amount it stands for, so two that differ only in scale are one amount
            // — the rule `Values.equal` states for the run-time values.
            case ObservedValue.Decimal x -> same(path,
                    x.value().compareTo(((ObservedValue.Decimal) o).value()) == 0, a, o, position);
            case ObservedValue.Text x ->
                    same(path, x.value().equals(((ObservedValue.Text) o).value()), a, o, position);
            case ObservedValue.Temporal x ->
                    same(path, x.iso().equals(((ObservedValue.Temporal) o).iso()), a, o, position);
            default -> new Mismatch(path, Reason.UNREADABLE, a, o, position);
        };
    }

    private static Mismatch same(String path, boolean equal, Asserted a, ObservedValue o,
                                 Type position) {
        return equal ? null : new Mismatch(path, Reason.VALUE, a, o, position);
    }

    /**
     * Two constructions. The names first, because a value is of its type before it is anything else:
     * a {@code Receipt} whose {@code total} the row wrote as a number and one whose {@code total} is
     * an {@code AmountN} are not one value written two ways.
     */
    private Mismatch constructed(String path, Asserted a, Asserted.Built built, ObservedValue o,
                                 Type position) {
        if (!(o instanceof ObservedValue.Constructed b) || !built.type().equals(b.type())) {
            return new Mismatch(path, Reason.TYPE, a, o, position);
        }
        Set<String> names = new LinkedHashSet<>(built.fields().keySet());
        names.addAll(b.fields().keySet());
        for (String name : names) {
            Asserted x = built.fields().get(name);
            ObservedValue y = b.field(name);
            if (x == null || y == null) {
                return new Mismatch(path + "." + name, Reason.SHAPE, a, o, position);
            }
            // The child's position comes from what this value's own type declares that field to be,
            // so nothing outside the value supplies one for what stands under it.
            Mismatch under = at(path + "." + name, x, y, fieldType(built.type(), name));
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
     * Two sequences, ordered or not as what they are says. A {@code List} is its elements in order and
     * a {@code Set} is its elements; the answer is whichever its declaration made it, and the row is
     * whichever it wrote — a row that wrote neither is read at the answer's, since {@code [ 1 ]} is
     * how both are written and states no preference between them.
     */
    private Mismatch sequence(String path, Asserted a, Asserted.Elements xs, ObservedValue o,
                              Type position) {
        if (!(o instanceof ObservedValue.Sequence ys)) {
            return new Mismatch(path, Reason.TYPE, a, o, position);
        }
        Type open = NeutralForm.open(position);
        Asserted.Container answered = open instanceof Type.SetOf ? Asserted.Container.SET
                : open instanceof Type.ListOf ? Asserted.Container.LIST : Asserted.Container.UNSTATED;
        if (xs.stated() != Asserted.Container.UNSTATED && answered != Asserted.Container.UNSTATED
                && xs.stated() != answered) {
            return new Mismatch(path, Reason.TYPE, a, o, position);
        }
        Asserted.Container reading = xs.stated() != Asserted.Container.UNSTATED ? xs.stated() : answered;
        Type element = switch (open) {
            case Type.ListOf l -> l.element();
            case Type.SetOf s -> s.element();
            case null, default -> null;
        };
        if (xs.elements().size() != ys.elements().size()) {
            return new Mismatch(path, Reason.SHAPE, a, o, position);
        }
        if (reading == Asserted.Container.SET) {
            return unordered(path, xs.elements(), ys.elements(), element, a, o, position);
        }
        for (int i = 0; i < xs.elements().size(); i++) {
            Mismatch under = at(path + "[" + i + "]", xs.elements().get(i), ys.elements().get(i),
                    element);
            if (under != null) {
                return under;
            }
        }
        return null;
    }

    /** A set: each element of one stands for one of the other, and which one is not part of the value. */
    private Mismatch unordered(String path, List<Asserted> xs, List<ObservedValue> ys, Type element,
                               Asserted a, ObservedValue o, Type position) {
        List<ObservedValue> left = new ArrayList<>(ys);
        for (Asserted x : xs) {
            boolean found = false;
            for (int i = 0; i < left.size(); i++) {
                if (at(path, x, left.get(i), element) == null) {
                    left.remove(i);
                    found = true;
                    break;
                }
            }
            if (!found) {
                return new Mismatch(path, Reason.SHAPE, a, o, position);
            }
        }
        return null;
    }

    /**
     * Two maps, matched by key rather than looked up by one. A key is the same key under the same rule
     * everything else here is compared by, which a hash lookup would answer with Java's equality — and
     * a key written under a name is not the base it wraps.
     */
    private Mismatch mapping(String path, Asserted a, Asserted.Entries xs, ObservedValue o,
                             Type position) {
        if (!(o instanceof ObservedValue.Mapping ys)) {
            return new Mismatch(path, Reason.TYPE, a, o, position);
        }
        Type open = NeutralForm.open(position);
        Type key = open instanceof Type.MapOf m ? m.key() : null;
        Type value = open instanceof Type.MapOf m ? m.value() : null;
        if (xs.entries().size() != ys.entries().size()) {
            return new Mismatch(path, Reason.SHAPE, a, o, position);
        }
        List<ObservedValue.Entry> left = new ArrayList<>(ys.entries());
        for (Asserted.Entry entry : xs.entries()) {
            int found = -1;
            for (int i = 0; i < left.size(); i++) {
                if (at(path, entry.key(), left.get(i).key(), key) == null) {
                    found = i;
                    break;
                }
            }
            if (found < 0) {
                return new Mismatch(path, Reason.SHAPE, a, o, position);
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
