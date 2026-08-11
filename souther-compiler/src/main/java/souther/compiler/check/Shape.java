package souther.compiler.check;

import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What a type is, once the names wrapped round it are off.
 *
 * <p>{@link Type} is sealed and can be switched exhaustively already, and one place does
 * ({@code TypeOps.answers}). That exhaustiveness runs out exactly where the readers of a position go
 * wrong: {@link Type.Ref} is one constructor standing for four things — a unit data, a record, a sum,
 * and a newtype — so a walk that has answered every constructor of {@code Type} has still not
 * answered every kind of position. This splits that one constructor, which is the whole reason it
 * exists.
 *
 * <p><b>There is no newtype case, and there must not be one.</b> A newtype is the value it wraps
 * (spec §primitives), so what a position is, is what its base is; the names it wears are how that
 * value is written and observed at this position, and they belong to {@link TypeView#wrappers}
 * rather than here. A {@code Newtype} case would let each reader decide again whether to look
 * through it, which is what left a {@code data StageN = Stage} with no classes while the line drawn
 * on the same position read straight through the name.
 *
 * <p>Nothing here says what a position divides into or what may be written at it. Those are
 * questions asked of a shape, by readers that must answer every case of it.
 */
public sealed interface Shape {

    /** A primitive, written as itself. */
    record Scalar(Type.Prim prim) implements Shape {}

    /** A data with no contents: one value, which is which case it is. */
    record Unit(TypeName name) implements Shape {}

    /** A data with fields, and what they are. */
    record Product(TypeName name, Map<String, Type> fields) implements Shape {
        public Product {
            fields = Map.copyOf(fields);
        }
    }

    /** A declared sum, {@code data S = A | B}. */
    record Sum(TypeName name) implements Shape {}

    /** A union nobody named — what a branch widened to, or a behavior's written answer. Told apart
     *  from {@link Sum} because it has no declaration to be read off. */
    record Cases(Set<TypeName> members) implements Shape {
        public Cases {
            members = Set.copyOf(members);
        }
    }

    /** A {@code List} or a {@code Set}, and what it holds. Which of the two is the declared type's
     *  to say — the values are the same either way, and how they are written is not. */
    record Sequence(Kind kind, Type element) implements Shape {

        public enum Kind { LIST, SET }
    }

    /** A {@code Map}, by what it is keyed by and what it holds. */
    record Mapping(Type key, Type value) implements Shape {}

    /** An {@code Option}, and what it holds when it holds anything. */
    record Optional(Type element) implements Shape {}

    /** A tuple, which carries values through a computation and crosses nothing. */
    record Tuple(List<Type> elements) implements Shape {
        public Tuple {
            elements = List.copyOf(elements);
        }
    }

    /** A function. */
    record Function(List<Type> params, Type result) implements Shape {
        public Function {
            params = List.copyOf(params);
        }
    }

    /**
     * A type variable: what stands here is decided by each application, so nothing about the values
     * at this position is settled yet.
     *
     * <p>Not {@link Nothing}. A variable will be some type, and a reader that meets one is early
     * rather than at a position there is nothing to say about.
     */
    record Undecided() implements Shape {}

    /**
     * The bottom of an empty collection, the type of an expression that answers nothing, and the
     * type of something the compiler could not work out. Grouped because no reader tells them apart:
     * each stands for a type rather than being one, and the module carrying the third has already
     * been told why.
     */
    record Nothing() implements Shape {}

    /**
     * A name that denotes no declaration this can read, or a newtype whose {@code value} it could
     * not reach. Its own case rather than {@link Nothing}: what is missing is a declaration, which
     * is a fact about what was resolved and not about the values at the position.
     */
    record Unresolved(TypeName name) implements Shape {}
}
