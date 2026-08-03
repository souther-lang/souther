package souther.compiler.check;

import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;

/**
 * Two readings of one value, taken together.
 *
 * <p>This is not a unification. A unification binds a variable so that everything downstream reads
 * the type it was bound to, and it is asked in one direction — a declared parameter against the
 * argument given for it. Two candidates for one helper parameter are neither: they are the same
 * value read at two positions, so what one of them states and the other leaves open is stated, and
 * neither side is the one being checked against the other. Nothing is bound by asking, so a merge
 * that does not go through answers with nothing rather than leaving a binding behind.
 *
 * <p>A variable is what a reading leaves open, so it yields to whatever the other reading says —
 * including another variable, since both readings are of one value and a value has one type. What
 * cannot be merged is two different answers about what the value <em>is</em>: a {@code List} and a
 * {@code Set} are not two readings of one thing.
 */
final class CandidateMerge {

    private CandidateMerge() {}

    /** The two readings as one type, or null where they say different things about the value. */
    static Type of(Type left, Type right) {
        if (left == null || right == null) {
            return null;
        }
        if (left.equals(right)) {
            return left;
        }
        if (left instanceof Type.Var) {
            return right;   // the left reading left this open; the right one says more
        }
        if (right instanceof Type.Var) {
            return left;
        }
        return switch (left) {
            case Type.ListOf l when right instanceof Type.ListOf r -> map(Type::list, l.element(), r.element());
            case Type.SetOf l when right instanceof Type.SetOf r -> map(Type::set, l.element(), r.element());
            case Type.OptionOf l when right instanceof Type.OptionOf r ->
                    map(Type::option, l.element(), r.element());
            case Type.MapOf l when right instanceof Type.MapOf r -> {
                Type key = of(l.key(), r.key());
                Type value = of(l.value(), r.value());
                yield key == null || value == null ? null : Type.map(key, value);
            }
            case Type.TupleOf l when right instanceof Type.TupleOf r
                    && l.elements().size() == r.elements().size() -> {
                List<Type> merged = new ArrayList<>();
                for (int i = 0; i < l.elements().size(); i++) {
                    Type e = of(l.elements().get(i), r.elements().get(i));
                    if (e == null) {
                        yield null;
                    }
                    merged.add(e);
                }
                yield Type.tuple(merged);
            }
            // A function type is never a candidate (a function-typed parameter is written), and two
            // unequal names, primitives or unions are two answers rather than one left open.
            default -> null;
        };
    }

    private static Type map(java.util.function.UnaryOperator<Type> wrap, Type left, Type right) {
        Type element = of(left, right);
        return element == null ? null : wrap.apply(element);
    }
}
