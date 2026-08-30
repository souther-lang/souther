package souther.compiler.observe;

import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Whether what was stated and what was answered are the same value, and where they are not.
 *
 * <p>The two sides are not one kind of thing and are not read as one. {@link Asserted} is what a
 * text wrote, carrying the names and the forms it wrote them under; {@link ObservedValue} is what a
 * value turned out to be. Two values differ when their types differ as much as when their contents
 * do, and saying which is the whole reason this is not equality over the run-time objects: those
 * are compared as values of one type, and the question here is whether they are of one type at all.
 *
 * <p>{@code position} is what the declaration says stands here, so it says what the <em>answer</em>
 * is: an {@link ObservedValue.Sequence} is a {@code List} and a {@code Set} alike, and which one it
 * is comes from the type that produced it. It says nothing about what was stated. A text that wrote
 * which collection it meant is held to that, and one that did not — {@code [ 1 ]} is how both are
 * written — is read at what the answer is, since there is nothing else for it to be.
 *
 * <p>What it reads of the declarations is one question ({@link ValueTypes}), so this is the same
 * comparison wherever it is made: by the compile that read the text, and by an output holding what
 * that compile decided.
 */
final class ValueMatch {

    private final ValueTypes types;

    ValueMatch(ValueTypes types) {
        this.types = types;
    }

    /**
     * Whether {@code answered} is what {@code stated} states.
     *
     * <p>The two grains in one place, so that what being the same answer means is settled once: a
     * reader that told them apart itself would have the other grain's comparison somewhere else,
     * and two comparisons of one statement can disagree.
     */
    Verdict verdict(Expectation stated, ObservedValue answered, Position answers) {
        return switch (stated) {
            case Expectation.TheValue(Asserted value) -> {
                Mismatch differs = compare(value, answered, answers);
                yield differs == null ? Verdict.HELD : new Verdict.NotHeld(differs);
            }
            // The case, and nothing under it: there is no value under a case to compare, and
            // holding a whole value against one would report a difference nobody stated. Which case
            // an answer is is the declaration it is of, which the reading that produced the answer
            // already settled.
            case Expectation.TheCase(souther.compiler.types.TypeSymbol name) -> {
                if (answered.unread() != null) {
                    yield new Verdict.NotHeld(new Mismatch(List.of(), Mismatch.Reason.UNREADABLE,
                            stated, answered, answers));
                }
                yield name.equals(answered.declaredAs()) ? Verdict.HELD
                        : new Verdict.NotHeld(new Mismatch(List.of(), Mismatch.Reason.TYPE, stated,
                                answered, answers));
            }
        };
    }

    /** Null where the two are the same value. */
    Mismatch compare(Asserted stated, ObservedValue observed, Position position) {
        return at(List.of(), stated, observed, position);
    }

    private Mismatch at(List<PathElement> path, Asserted a, ObservedValue o, Position position) {
        if (o.unread() != null) {
            return differs(path, Mismatch.Reason.UNREADABLE, a, o, position);
        }
        return switch (a) {
            case Asserted.Value(ObservedValue v) -> leaf(path, a, v, o, position);
            case Asserted.Built built -> constructed(path, a, built, o, position);
            case Asserted.Elements elements -> sequence(path, a, elements, o, position);
            case Asserted.Entries entries -> mapping(path, a, entries, o, position);
        };
    }

    private static Mismatch differs(List<PathElement> path, Mismatch.Reason reason, Asserted a,
                                    ObservedValue o, Position position) {
        return new Mismatch(path, reason, new Expectation.TheValue(a), o, position);
    }

    private static List<PathElement> into(List<PathElement> path, PathElement step) {
        List<PathElement> out = new ArrayList<>(path);
        out.add(step);
        return List.copyOf(out);
    }

    /** A value with no parts against one. Absence is neither a type nor a value of one: a position
     *  holds nothing or holds something, and that is its own answer. */
    private Mismatch leaf(List<PathElement> path, Asserted a, ObservedValue v, ObservedValue o,
                          Position position) {
        if (v.unread() != null) {
            return differs(path, Mismatch.Reason.UNREADABLE, a, o, position);
        }
        if (v instanceof ObservedValue.Absent || o instanceof ObservedValue.Absent) {
            return v instanceof ObservedValue.Absent && o instanceof ObservedValue.Absent
                    ? null : differs(path, Mismatch.Reason.ABSENCE, a, o, position);
        }
        // Of one type before anything else, and which type a written value with no parts is has one
        // answer for every reader of it. A text writing `1` where a `Decimal` came out wrote an `Int`
        // — the difference is written in the language, and reading a whole number as an amount is
        // what a boundary does and not what the text did.
        Type.Prim stated = v.primitive();
        Type.Prim answered = o.primitive();
        if (stated == null || stated != answered) {
            return v instanceof ObservedValue.Unit x && o instanceof ObservedValue.Unit y
                    && x.type().equals(y.type())
                    ? null : differs(path, Mismatch.Reason.TYPE, a, o, position);
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
            default -> differs(path, Mismatch.Reason.UNREADABLE, a, o, position);
        };
    }

    private static Mismatch same(List<PathElement> path, boolean equal, Asserted a, ObservedValue o,
                                 Position position) {
        return equal ? null : differs(path, Mismatch.Reason.VALUE, a, o, position);
    }

    /**
     * Two constructions. The names first, because a value is of its type before it is anything else:
     * a {@code Receipt} whose {@code total} was written as a number and one whose {@code total} is
     * an {@code AmountN} are not one value written two ways.
     */
    private Mismatch constructed(List<PathElement> path, Asserted a, Asserted.Built built,
                                 ObservedValue o, Position position) {
        if (!(o instanceof ObservedValue.Constructed b) || !built.type().equals(b.type())) {
            return differs(path, Mismatch.Reason.TYPE, a, o, position);
        }
        Set<String> names = new LinkedHashSet<>(built.fields().keySet());
        names.addAll(b.fields().keySet());
        for (String name : names) {
            Asserted x = built.fields().get(name);
            ObservedValue y = b.field(name);
            if (x == null || y == null) {
                // At the construction and not at the field: what differs is which places the two
                // hold, which is a fact about them rather than about a place one of them has not
                // got. Said at the field, the path would name somewhere the values beside it are
                // not from — and there is no value there to name it with.
                return differs(path, Mismatch.Reason.SHAPE, a, o, position);
            }
            List<PathElement> inside = into(path, new PathElement.Field(name));
            // The child's position comes from what this value's own type declares that field to be,
            // so nothing outside the value supplies one for what stands under it.
            Mismatch under = at(inside, x, y, types.field(built.type(), name));
            if (under != null) {
                return under;
            }
        }
        return null;
    }

    /**
     * Two sequences, ordered or not as what they are says. A {@code List} is its elements in order and
     * a {@code Set} is its elements; the answer is whichever its declaration made it, and what was
     * stated is whichever it wrote — a text that wrote neither is read at the answer's, since
     * {@code [ 1 ]} is how both are written and states no preference between them.
     */
    private Mismatch sequence(List<PathElement> path, Asserted a, Asserted.Elements xs,
                              ObservedValue o, Position position) {
        if (!(o instanceof ObservedValue.Sequence ys)) {
            return differs(path, Mismatch.Reason.TYPE, a, o, position);
        }
        Type open = position.opened() instanceof Position.At(Type type) ? type : null;
        Asserted.Container answered = open instanceof Type.SetOf ? Asserted.Container.SET
                : open instanceof Type.ListOf ? Asserted.Container.LIST : Asserted.Container.UNSTATED;
        if (xs.stated() != Asserted.Container.UNSTATED && answered != Asserted.Container.UNSTATED
                && xs.stated() != answered) {
            return differs(path, Mismatch.Reason.TYPE, a, o, position);
        }
        Asserted.Container reading = xs.stated() != Asserted.Container.UNSTATED ? xs.stated() : answered;
        Position element = switch (open) {
            case Type.ListOf l -> Position.at(l.element());
            case Type.SetOf s -> Position.at(s.element());
            case null, default -> Position.UNREAD;
        };
        if (xs.elements().size() != ys.elements().size()) {
            return differs(path, Mismatch.Reason.SHAPE, a, o, position);
        }
        if (reading == Asserted.Container.SET) {
            return unordered(path, xs.elements(), ys.elements(), element, a, o, position);
        }
        for (int i = 0; i < xs.elements().size(); i++) {
            Mismatch under = at(into(path, new PathElement.Index(i)), xs.elements().get(i),
                    ys.elements().get(i), element);
            if (under != null) {
                return under;
            }
        }
        return null;
    }

    /** A set: each element of one stands for one of the other, and which one is not part of the value. */
    private Mismatch unordered(List<PathElement> path, List<Asserted> xs, List<ObservedValue> ys,
                               Position element, Asserted a, ObservedValue o, Position position) {
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
                return differs(path, Mismatch.Reason.SHAPE, a, o, position);
            }
        }
        return null;
    }

    /**
     * Two maps, matched by key rather than looked up by one. A key is the same key under the same rule
     * everything else here is compared by, which a hash lookup would answer with Java's equality — and
     * a key written under a name is not the base it wraps.
     */
    private Mismatch mapping(List<PathElement> path, Asserted a, Asserted.Entries xs,
                             ObservedValue o, Position position) {
        if (!(o instanceof ObservedValue.Mapping ys)) {
            return differs(path, Mismatch.Reason.TYPE, a, o, position);
        }
        Position key = position.key();
        Position value = position.value();
        if (xs.entries().size() != ys.entries().size()) {
            return differs(path, Mismatch.Reason.SHAPE, a, o, position);
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
                return differs(path, Mismatch.Reason.SHAPE, a, o, position);
            }
            ObservedValue.Entry match = left.remove(found);
            // The key the entry was found by, which says which entry this is. Every leaf of it was
            // compared to get here, so it is a value that is there — which is what a step naming an
            // entry has to be.
            Mismatch under = at(into(path, new PathElement.Key(entry.key())), entry.value(),
                    match.value(), value);
            if (under != null) {
                return under;
            }
        }
        return null;
    }
}
