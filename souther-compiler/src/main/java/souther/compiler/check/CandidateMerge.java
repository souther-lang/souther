package souther.compiler.check;

import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Two readings of one value, taken together.
 *
 * <p>This is not a unification. A unification binds a variable so that everything downstream reads
 * the type it was bound to, and it is asked in one direction — a declared parameter against the
 * argument given for it. Two candidates for one helper parameter are neither: they are the same
 * value read at two positions, so what one of them states and the other leaves open is stated, and
 * neither side is the one being checked against the other. Nothing outside this call is bound by
 * asking, so a merge that does not go through answers with nothing and leaves no binding behind.
 *
 * <p>What a variable stands for is still held while the two are read, in both directions. A variable
 * is what a reading leaves open, so it yields to whatever the other reading says there — but it says
 * the same thing everywhere it appears, so a second appearance has to meet what the first one met.
 * {@code ('a, 'a)} read against {@code (Int, String)} is not {@code (Int, String)}: one reading says
 * the two positions hold one type and the other says they hold two, and that is two answers rather
 * than one left open. Holding both directions is what makes the answer the same whichever reading is
 * given first.
 *
 * <p>What cannot be merged either way is two different answers about what the value <em>is</em>: a
 * {@code List} and a {@code Set} are not two readings of one thing.
 */
final class CandidateMerge {

    private CandidateMerge() {}

    /** The two readings as one type, or null where they say different things about the value. */
    static Type of(Type left, Type right) {
        return merge(left, right, new HashMap<>(), new HashMap<>());
    }

    /**
     * {@code stands} and {@code forThat} are what each side's variables have been read as, by name.
     * Both are kept: a variable on either side means the same thing at every position it stands in,
     * and asking only of the side that happens to be written first makes the answer depend on which
     * reading was found first.
     */
    private static Type merge(Type left, Type right,
                              Map<String, Type> stands, Map<String, Type> forThat) {
        if (left == null || right == null) {
            return null;
        }
        if (left instanceof Type.Var lv) {
            return met(lv, right, stands, forThat);
        }
        if (right instanceof Type.Var rv) {
            return met(rv, left, forThat, stands);
        }
        return switch (left) {
            case Type.ListOf l when right instanceof Type.ListOf r ->
                    wrap(Type::list, l.element(), r.element(), stands, forThat);
            case Type.SetOf l when right instanceof Type.SetOf r ->
                    wrap(Type::set, l.element(), r.element(), stands, forThat);
            case Type.OptionOf l when right instanceof Type.OptionOf r ->
                    wrap(Type::option, l.element(), r.element(), stands, forThat);
            case Type.MapOf l when right instanceof Type.MapOf r -> {
                Type key = merge(l.key(), r.key(), stands, forThat);
                Type value = merge(l.value(), r.value(), stands, forThat);
                yield key == null || value == null ? null : Type.map(key, value);
            }
            case Type.TupleOf l when right instanceof Type.TupleOf r
                    && l.elements().size() == r.elements().size() -> {
                List<Type> merged = new ArrayList<>();
                for (int i = 0; i < l.elements().size(); i++) {
                    Type e = merge(l.elements().get(i), r.elements().get(i), stands, forThat);
                    if (e == null) {
                        yield null;
                    }
                    merged.add(e);
                }
                yield Type.tuple(merged);
            }
            // A function type is never a candidate (a function-typed parameter is written), and two
            // unequal names, primitives or unions are two answers rather than one left open.
            default -> left.equals(right) ? left : null;
        };
    }

    /**
     * What {@code v} standing where {@code other} stands comes to, given everywhere else it stands,
     * or null where the two cannot be one thing. Recorded in both directions, so a variable on the
     * other side is held to the same rule.
     *
     * <p>Where it stood somewhere already, the two readings of it are themselves two readings of one
     * value and are merged: {@code Map<'a, 'a>} against {@code Map<String, 'b>} says the key is a
     * String and then that the value is `'b`, and `'b` is what the second reading leaves open, so
     * the answer is a Map of String to String rather than a disagreement.
     *
     * <p>A variable cannot stand for something holding itself. Nothing built from a value contains
     * that value, so a reading that says so is not one this can take.
     */
    private static Type met(Type.Var v, Type other,
                            Map<String, Type> its, Map<String, Type> theirs) {
        if (!v.equals(other) && Type.mentions(other, x -> x.equals(v))) {
            return null;   // `'a` and `List<'a>` are not two readings of one value
        }
        Type.Var ov = other instanceof Type.Var o ? o : null;
        Type mine = stoodFor(its, v);
        Type yours = ov == null ? stoodFor(theirs, other) : stoodFor(theirs, ov);
        Type both;
        if (mine instanceof Type.Var one && yours instanceof Type.Var another) {
            // Both readings leave this position open, and either name denotes the value equally
            // well. One is taken, by name, so the answer is a function of the two readings and not
            // of which was given first.
            both = one.name().compareTo(another.name()) <= 0 ? one : another;
        } else if (mine instanceof Type.Var) {
            both = yours;
        } else if (yours instanceof Type.Var) {
            both = mine;
        } else {
            // Neither leaves it open, so what each has been read as is itself two readings of one
            // value. Both are headed by a constructor, so this descends rather than coming back here.
            both = merge(mine, yours, its, theirs);
            if (both == null) {
                return null;
            }
        }
        its.put(v.name(), both);
        if (ov != null) {
            theirs.put(ov.name(), both);
        }
        return both;
    }

    /**
     * What {@code t} has been read as, following what stands for what until something is not a
     * variable or nothing more is said. A variable nothing has said anything about answers itself.
     */
    private static Type stoodFor(Map<String, Type> read, Type t) {
        java.util.Set<String> seen = new java.util.HashSet<>();
        Type at = t;
        while (at instanceof Type.Var v && seen.add(v.name())) {
            Type next = read.get(v.name());
            if (next == null || next.equals(at)) {
                return at;
            }
            at = next;
        }
        return at;
    }

    private static Type wrap(java.util.function.UnaryOperator<Type> hold, Type left, Type right,
                             Map<String, Type> stands, Map<String, Type> forThat) {
        Type element = merge(left, right, stands, forThat);
        return element == null ? null : hold.apply(element);
    }
}
