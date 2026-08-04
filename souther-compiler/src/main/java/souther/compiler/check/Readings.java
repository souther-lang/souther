package souther.compiler.check;

import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Every reading of one helper parameter, and what they settle between them.
 *
 * <p>This is unification, done locally and symmetrically. Variables are settled to types and to each
 * other, constructors are taken apart, a variable is refused a type it stands inside, and what was
 * settled is substituted through at the end. What it is not is {@link TypeOps#unify}: that one checks
 * an argument against a declared parameter, in that direction, and hands its bindings on to the rest
 * of the call. Here there is no direction — several readings of one value, none of them the one being
 * checked — and nothing settled here outlives the parameter, so a reading that does not go through
 * leaves nothing behind.
 *
 * <p>Readings are given one at a time as the walk finds them, and the answer is asked for once at the
 * end. That is the reason for the two steps rather than a convenience: a reading that says what a
 * variable is may arrive after the readings that used it, so what is being built while they arrive is
 * not the answer. {@code a}, then {@code (b, b)}, then {@code (b, Int)} says the value is a pair of
 * Ints, and only the last reading says which — so it is settled through the whole shape once every
 * reading is in, not written into whatever had been assembled by the time it arrived.
 */
final class Readings {

    /** What each variable is settled to. A variable nothing has settled is not in here. */
    private final Map<Type.Open, Type> settled = new HashMap<>();
    private Type shape;
    private boolean refused;
    /** What was settled before this parameter began, for a parameter that turns out to settle
     * nothing. */
    private Map<Type.Open, Type> held = Map.of();

    /**
     * Starts on another parameter. What the readings have settled about a variable is kept: two
     * parameters of one helper are read in one body, and a variable one of them settled to another is
     * settled for both — {@code let has (xs, y) = List.member(y, xs)} learns while reading {@code xs}
     * that what the expansion left open and what the call inside it left open are one thing, and
     * {@code y} is the parameter that needs to know.
     */
    void forParameter() {
        shape = null;
        refused = false;
        held = Map.copyOf(settled);
    }

    /** {@code t} with what the readings have settled written through it. */
    Type asSettled(Type t) {
        return settledSoFar(t);
    }

    /** Takes one more reading of the value. */
    void add(Type reading) {
        if (refused) {
            return;
        }
        shape = shape == null ? reading : unify(shape, reading);
        if (shape == null) {
            // Readings that cannot be one value settle nothing. A constructor is taken apart one
            // position at a time, so what the positions before the disagreement settled is written
            // while it is still open whether they are one value at all — and this parameter having
            // no answer is not evidence for the next one. What was settled before this parameter
            // began is what stands.
            refused = true;
            settled.clear();
            settled.putAll(held);
        }
    }

    /** Every reading given, as one type, or null where they cannot be one value. */
    Type answer() {
        return refused || shape == null ? null : settledSoFar(shape);
    }

    /** {@code readings} taken together — the whole question asked at once. */
    static Type of(List<Type> readings) {
        Readings all = new Readings();
        for (Type reading : readings) {
            all.add(reading);
        }
        return all.answer();
    }

    static Type of(Type left, Type right) {
        return of(List.of(left, right));
    }

    /**
     * {@code left} and {@code right} as one type, settling what that settles, or null where they
     * cannot be one value. Each side is taken as far as what is already settled says, so what is
     * compared and what is taken apart is what the readings have come to rather than how they were
     * written. What this returns is what is known at this point; what is known at the end is
     * {@link #answer}.
     */
    private Type unify(Type left, Type right) {
        if (left == null || right == null) {
            return null;
        }
        Type l = settledSoFar(left);
        Type r = settledSoFar(right);
        if (l.equals(r)) {
            return l;
        }
        if (l instanceof Type.Open lv && r instanceof Type.Open rv) {
            // Either name denotes the value equally well, so one is settled to the other by name and
            // the answer is what the readings say rather than which of them was given first.
            return lv.toString().compareTo(rv.toString()) <= 0 ? bind(rv, lv) : bind(lv, rv);
        }
        if (l instanceof Type.Open lv) {
            return bind(lv, r);
        }
        if (r instanceof Type.Open rv) {
            return bind(rv, l);
        }
        return switch (l) {
            case Type.ListOf a when r instanceof Type.ListOf b ->
                    hold(Type::list, a.element(), b.element());
            case Type.SetOf a when r instanceof Type.SetOf b ->
                    hold(Type::set, a.element(), b.element());
            case Type.OptionOf a when r instanceof Type.OptionOf b ->
                    hold(Type::option, a.element(), b.element());
            case Type.MapOf a when r instanceof Type.MapOf b -> {
                Type key = unify(a.key(), b.key());
                Type value = unify(a.value(), b.value());
                yield key == null || value == null ? null : Type.map(key, value);
            }
            case Type.TupleOf a when r instanceof Type.TupleOf b
                    && a.elements().size() == b.elements().size() -> {
                List<Type> both = new ArrayList<>();
                for (int i = 0; i < a.elements().size(); i++) {
                    Type e = unify(a.elements().get(i), b.elements().get(i));
                    if (e == null) {
                        yield null;
                    }
                    both.add(e);
                }
                yield Type.tuple(both);
            }
            // A function type is never a reading of a parameter (a function-typed parameter is
            // written), and two unequal names, primitives or unions are two answers about what the
            // value is rather than one of them leaving it open.
            default -> null;
        };
    }

    /**
     * {@code variable} settled to {@code type}, or null where it cannot be. One variable and one
     * type, so there is one question to ask: does the variable stand inside what it would be settled
     * to. {@code type} has already been taken as far as what is settled says, so a variable reached
     * only through another is found — {@code a} is a list of {@code b}, and {@code a} is {@code b},
     * settles {@code b} to a list of {@code b}, which is a value that would have to hold itself.
     */
    private Type bind(Type.Open variable, Type type) {
        if (Type.mentions(type, variable::equals)) {
            return null;
        }
        settled.put(variable, type);
        return type;
    }

    /**
     * {@code t} with every variable in it replaced by what it is settled to, following what is
     * settled to what until nothing more is said.
     *
     * <p>{@code following} is the one chain being followed, not everything seen: it ends a cycle of
     * variables settled to each other, and a position beside this one is another chain. Sharing it
     * would leave the second of two positions holding one variable unsettled.
     */
    private Type settledSoFar(Type t) {
        return settledSoFar(t, new HashSet<>());
    }

    private Type settledSoFar(Type t, Set<Type.Open> following) {
        if (t instanceof Type.Open v) {
            Type next = settled.get(v);
            if (next == null || next.equals(v) || !following.add(v)) {
                return v;
            }
            Type through = settledSoFar(next, following);
            following.remove(v);
            return through;
        }
        return switch (t) {
            case Type.ListOf l -> Type.list(settledSoFar(l.element(), following));
            case Type.SetOf s -> Type.set(settledSoFar(s.element(), following));
            case Type.OptionOf o -> Type.option(settledSoFar(o.element(), following));
            case Type.MapOf m -> Type.map(settledSoFar(m.key(), following),
                    settledSoFar(m.value(), following));
            case Type.TupleOf tu -> {
                List<Type> at = new ArrayList<>();
                for (Type e : tu.elements()) {
                    at.add(settledSoFar(e, following));
                }
                yield Type.tuple(at);
            }
            default -> t;
        };
    }

    private Type hold(java.util.function.UnaryOperator<Type> wrap, Type left, Type right) {
        Type inside = unify(left, right);
        return inside == null ? null : wrap.apply(inside);
    }
}
