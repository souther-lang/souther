package souther.compiler.check;

import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Every reading of one value, taken together.
 *
 * <p>This is not a unification. A unification binds a variable so that everything downstream reads
 * the type it was bound to, and it is asked in one direction — a declared parameter against the
 * argument given for it. Several readings of one helper parameter are neither: they are the same
 * value read at several positions, so what one of them states and another leaves open is stated, and
 * none of them is the one being checked against the others. Nothing outside this stands for anything
 * afterwards, so readings that cannot be one value answer with nothing and leave nothing behind.
 *
 * <p>What a variable stands for is held for as long as the readings are being taken, and not for one
 * pair of them. A variable says one thing everywhere it appears, and the reading that says what it is
 * may arrive after the readings that used it: {@code (a, b)} and then {@code (b, a)} say the two
 * positions hold one thing, and {@code (Int, a)} arriving third says what that thing is. Taking the
 * readings two at a time and keeping only the type would drop that — the answer would depend on which
 * pair was put together first, and a value that holds itself could be assembled in one order and
 * refused in another.
 *
 * <p>What cannot be read as one value is two different answers about what it <em>is</em>: a
 * {@code List} and a {@code Set} are not two readings of one thing, and neither is a value that would
 * have to hold itself.
 */
final class CandidateMerge {

    /** What each variable has been read as. A variable standing for itself stands for nothing yet. */
    private final Map<Type.Var, Type> stands = new HashMap<>();
    private Type taken;
    private boolean refused;

    /** Everything given so far as one type, or null where it cannot be one value. */
    Type take(Type reading) {
        if (refused) {
            return null;
        }
        taken = taken == null ? reading : merge(taken, reading);
        refused = taken == null;
        return taken;
    }

    /** Starts again, holding nothing — the readings of one parameter are not another's. */
    void forget() {
        stands.clear();
        taken = null;
        refused = false;
    }

    /** {@code readings} taken together, for asking the whole question at once. */
    static Type of(List<Type> readings) {
        CandidateMerge one = new CandidateMerge();
        Type answer = null;
        for (Type reading : readings) {
            answer = one.take(reading);
        }
        return answer;
    }

    static Type of(Type left, Type right) {
        return of(List.of(left, right));
    }

    private Type merge(Type left, Type right) {
        if (left == null || right == null) {
            return null;
        }
        if (left instanceof Type.Var lv) {
            return met(lv, right);
        }
        if (right instanceof Type.Var rv) {
            return met(rv, left);
        }
        return switch (left) {
            case Type.ListOf l when right instanceof Type.ListOf r ->
                    wrap(Type::list, l.element(), r.element());
            case Type.SetOf l when right instanceof Type.SetOf r ->
                    wrap(Type::set, l.element(), r.element());
            case Type.OptionOf l when right instanceof Type.OptionOf r ->
                    wrap(Type::option, l.element(), r.element());
            case Type.MapOf l when right instanceof Type.MapOf r -> {
                Type key = merge(l.key(), r.key());
                Type value = merge(l.value(), r.value());
                yield key == null || value == null ? null : Type.map(key, value);
            }
            case Type.TupleOf l when right instanceof Type.TupleOf r
                    && l.elements().size() == r.elements().size() -> {
                List<Type> merged = new ArrayList<>();
                for (int i = 0; i < l.elements().size(); i++) {
                    Type e = merge(l.elements().get(i), r.elements().get(i));
                    if (e == null) {
                        yield null;
                    }
                    merged.add(e);
                }
                yield Type.tuple(merged);
            }
            // A function type is never a reading of a parameter (a function-typed parameter is
            // written), and two unequal names, primitives or unions are two answers rather than one
            // left open.
            default -> left.equals(right) ? left : null;
        };
    }

    /**
     * What {@code v} standing where {@code other} stands comes to, given everything each of them has
     * been read as, or null where the two cannot be one value.
     *
     * <p>Both are followed to what they come to before they are put together, so a variable that
     * stood for something is read <em>with</em> what it stands for now rather than compared to it,
     * and two variables standing for each other do not send this back and forth. What is put together
     * after that is headed by a constructor on both sides, so the merge descends.
     */
    private Type met(Type.Var v, Type other) {
        Type mine = stoodFor(v);
        Type yours = stoodFor(other);
        // A variable cannot stand for something holding it. Asked of what each side comes to, because
        // what holds it may hold it only through another variable — `a` is `b`, and `b` is a list of
        // `b`, is a value that would have to hold itself however the readings are assembled. Standing
        // for the very thing it comes to is not holding it.
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
            both = merge(mine, yours);
            if (both == null) {
                return null;
            }
        }
        stands.put(v, both);
        if (other instanceof Type.Var ov) {
            stands.put(ov, both);
        }
        return both;
    }

    /**
     * What {@code t} has been read as: every variable in it replaced by what it stands for, following
     * what stands for what until nothing more is said. A variable nothing has said anything about
     * answers itself.
     */
    private Type stoodFor(Type t) {
        return stoodFor(t, new java.util.HashSet<>());
    }

    private Type stoodFor(Type t, java.util.Set<Type.Var> seen) {
        if (t instanceof Type.Var v) {
            if (!seen.add(v)) {
                return v;
            }
            Type next = stands.get(v);
            return next == null || next.equals(v) ? v : stoodFor(next, seen);
        }
        return switch (t) {
            case Type.ListOf l -> Type.list(stoodFor(l.element(), seen));
            case Type.SetOf s -> Type.set(stoodFor(s.element(), seen));
            case Type.OptionOf o -> Type.option(stoodFor(o.element(), seen));
            case Type.MapOf m -> Type.map(stoodFor(m.key(), seen), stoodFor(m.value(), seen));
            case Type.TupleOf tu -> {
                List<Type> at = new ArrayList<>();
                for (Type e : tu.elements()) {
                    at.add(stoodFor(e, seen));
                }
                yield Type.tuple(at);
            }
            default -> t;
        };
    }

    private Type wrap(java.util.function.UnaryOperator<Type> hold, Type left, Type right) {
        Type element = merge(left, right);
        return element == null ? null : hold.apply(element);
    }
}
