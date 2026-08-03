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
 * <p>This solves constraints, and it is fair to call what it does unification — variables are held
 * equal to each other and bound to types, constructors are taken apart, a value is refused the chance
 * to hold itself, and what was settled is substituted through at the end. What it is not is
 * {@link TypeOps#unify}: that one checks an argument against a declared parameter, in that direction,
 * and hands its bindings on to the rest of the call. Here there is no direction — several readings of
 * one value, none of them the one being checked — and nothing it settles outlives the parameter, so a
 * reading that does not go through leaves nothing behind.
 *
 * <p>Readings are given one at a time as the walk finds them, and the answer is asked for once at the
 * end. That is the reason for the two steps rather than a convenience: a reading that says what a
 * variable is may arrive after the readings that used it, so what is being built while they arrive
 * is not the answer. {@code a}, then {@code (b, b)}, then {@code (b, Int)} says the value is a pair
 * of Ints, and only the last reading says which — so it is settled through the whole shape once every
 * reading is in, not written into whatever had been assembled by the time it arrived.
 */
final class Readings {

    /** What each variable has been settled to. A variable settled to itself is settled to nothing. */
    private final Map<Type.Var, Type> settled = new HashMap<>();
    private Type shape;
    private boolean refused;

    /** Takes one more reading of the value. */
    void add(Type reading) {
        if (refused) {
            return;
        }
        shape = shape == null ? reading : unify(shape, reading);
        refused = shape == null;
    }

    /** Every reading given, as one type, or null where they cannot be one value. */
    Type answer() {
        return refused || shape == null ? null : settledThrough(shape, new HashSet<>());
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
     * {@code left} and {@code right} as one type, recording what that settles, or null where they
     * cannot be one value. What it returns is what is known at this point; what is known at the end
     * is {@link #answer}.
     */
    private Type unify(Type left, Type right) {
        if (left == null || right == null) {
            return null;
        }
        if (left instanceof Type.Var lv) {
            return settle(lv, right);
        }
        if (right instanceof Type.Var rv) {
            return settle(rv, left);
        }
        return switch (left) {
            case Type.ListOf l when right instanceof Type.ListOf r ->
                    hold(Type::list, l.element(), r.element());
            case Type.SetOf l when right instanceof Type.SetOf r ->
                    hold(Type::set, l.element(), r.element());
            case Type.OptionOf l when right instanceof Type.OptionOf r ->
                    hold(Type::option, l.element(), r.element());
            case Type.MapOf l when right instanceof Type.MapOf r -> {
                Type key = unify(l.key(), r.key());
                Type value = unify(l.value(), r.value());
                yield key == null || value == null ? null : Type.map(key, value);
            }
            case Type.TupleOf l when right instanceof Type.TupleOf r
                    && l.elements().size() == r.elements().size() -> {
                List<Type> both = new ArrayList<>();
                for (int i = 0; i < l.elements().size(); i++) {
                    Type e = unify(l.elements().get(i), r.elements().get(i));
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
            default -> left.equals(right) ? left : null;
        };
    }

    /**
     * What {@code v} standing where {@code other} stands comes to, given what each of them is settled
     * to. Both are followed to what they come to before they are put together, so a variable settled
     * to something is read with it rather than compared to it, and two variables settled to each
     * other do not send this back and forth. What is put together after that is headed by a
     * constructor on both sides, so this descends.
     */
    private Type settle(Type.Var v, Type other) {
        Type mine = settledThrough(v, new HashSet<>());
        Type yours = settledThrough(other, new HashSet<>());
        // A variable cannot be settled to something holding it. Asked of what each side comes to,
        // because what holds it may hold it only through another variable — `a` is `b`, and `b` is a
        // list of `b`, is a value that would have to hold itself however the readings are given.
        // Being the very thing it comes to is not holding it.
        if (!yours.equals(mine) && Type.mentions(yours, x -> x.equals(v) || x.equals(mine))) {
            return null;
        }
        Type both;
        if (mine instanceof Type.Var one && yours instanceof Type.Var another) {
            // Both readings leave this position open, and either name denotes the value equally well.
            // One is taken, by name, so the answer is what the readings say and not what order they
            // were given in.
            both = one.name().compareTo(another.name()) <= 0 ? one : another;
        } else if (mine instanceof Type.Var) {
            both = yours;
        } else if (yours instanceof Type.Var) {
            both = mine;
        } else {
            both = unify(mine, yours);
            if (both == null) {
                return null;
            }
        }
        // Both the variables read here and what each of them already came to. A variable settled to
        // another is only reached through it, so settling the one in hand and not the one it came to
        // leaves the second still standing for itself wherever else it was read.
        settleTo(v, both);
        settleTo(mine, both);
        settleTo(other, both);
        settleTo(yours, both);
        return both;
    }

    private void settleTo(Type maybeVariable, Type both) {
        if (maybeVariable instanceof Type.Var v) {
            settled.put(v, both);
        }
    }

    /**
     * {@code t} with every variable in it replaced by what it is settled to, following what is
     * settled to what until nothing more is said. A variable nothing has settled answers itself.
     *
     * <p>{@code following} is the one chain being followed, not everything seen: it ends a cycle of
     * variables settled to each other, and a position beside this one is another chain. Sharing it
     * would leave the second of two positions holding one variable unsettled.
     */
    private Type settledThrough(Type t, Set<Type.Var> following) {
        if (t instanceof Type.Var v) {
            Type next = settled.get(v);
            if (next == null || next.equals(v) || !following.add(v)) {
                return v;
            }
            Type through = settledThrough(next, following);
            following.remove(v);
            return through;
        }
        return switch (t) {
            case Type.ListOf l -> Type.list(settledThrough(l.element(), following));
            case Type.SetOf s -> Type.set(settledThrough(s.element(), following));
            case Type.OptionOf o -> Type.option(settledThrough(o.element(), following));
            case Type.MapOf m -> Type.map(settledThrough(m.key(), following),
                    settledThrough(m.value(), following));
            case Type.TupleOf tu -> {
                List<Type> at = new ArrayList<>();
                for (Type e : tu.elements()) {
                    at.add(settledThrough(e, following));
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
