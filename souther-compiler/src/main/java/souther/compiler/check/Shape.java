package souther.compiler.check;

import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

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
 * <p><b>This is a total classification, and some of its cases are not value shapes.</b> A reading
 * that answers "a record", "a sum", "a list" for the types it knows and nothing for the rest is the
 * defect, not the base case: what a reader does with a type it cannot interpret is decided by the
 * reader, and every reader has decided it silently. So the failures to determine a shape are cases
 * here, of the same standing as the shapes, and a reader answering all of them has answered every
 * type it can be handed.
 *
 * <p>Which is why {@link Uninhabited}, {@link Bottom}, {@link Erroneous}, {@link Undecided} and
 * {@link Unresolved} are five cases and not one {@code Unknown}. Two of them say something about the
 * values — no value arrives, or the element type of an empty collection is not fixed yet — and three
 * say something about this compiler. Collapsing them would put a reader in the position of having to
 * tell a semantic fact from an analysis failure after the distinction was thrown away, which is the
 * shape of the defect this exists to remove: a position nothing could read was reported as one the
 * model divides no way.
 *
 * <p>Nothing here says what a position divides into or what may be written at it. Those are
 * questions asked of a shape, by readers that must answer every case of it — and a reader that finds
 * itself writing this switch out again wants a question of its own asked once, the way
 * {@link Carrier#ofValue} asks whether a line can be drawn, rather than a copy of this one.
 */
public sealed interface Shape permits Shape.PartitionInputShape, Shape.Cases, Shape.Tuple,
        Shape.Function, Shape.Uninhabited, Shape.Bottom, Shape.Erroneous, Shape.Undecided {

    /**
     * The shapes a position carrying a value can have.
     *
     * <p>A subset of the classification and not a second one: these are the same cases, grouped so
     * that a reader over positions can be held to all of them and to nothing else. What admits a
     * shape into it is the reader's own contract — the partition walk decides for itself, rather
     * than deriving the set from what a signature or a field admits, because those two disagree
     * (an {@code Option} may be a field and may not be a parameter) and neither is this question.
     *
     * <p>{@link Unresolved} is a member. It is a shape a position legitimately has — a declaration
     * reachable from itself compiles — and what a reader does with it is answer that it could not
     * be interpreted. Leaving it out would put a compiling model through a path that throws.
     */
    sealed interface PartitionInputShape extends Shape
            permits Scalar, Product, Sum, Sequence, Unit, Mapping, Optional, Unresolved {}

    /** A primitive, written as itself. */
    record Scalar(Type.Prim prim) implements PartitionInputShape {}

    /** A data with no contents: one value, which is which case it is. */
    record Unit(TypeSymbol name) implements PartitionInputShape {}

    /** A data with fields, and what they are, in the order the declaration writes them.
     *
     *  <p>The order is part of the answer, not an accident of the map: what a report names first
     *  and which field a row is built for first are read off it. So the copy keeps it — an
     *  unordered one would leave every reader depending on a hash. */
    record Product(TypeSymbol name, Map<String, Type> fields) implements PartitionInputShape {
        public Product {
            fields = java.util.Collections.unmodifiableMap(new java.util.LinkedHashMap<>(fields));
        }
    }

    /** A declared sum, {@code data S = A | B}. */
    record Sum(TypeSymbol name) implements PartitionInputShape {}

    /** A union nobody named — what a branch widened to, or a behavior's written answer. Told apart
     *  from {@link Sum} because it has no declaration to be read off. */
    record Cases(Set<TypeSymbol> members) implements Shape {
        public Cases {
            members = Set.copyOf(members);
        }
    }

    /** A {@code List} or a {@code Set}, and what it holds. Which of the two is the declared type's
     *  to say — the values are the same either way, and how they are written is not. */
    record Sequence(Kind kind, Type element) implements PartitionInputShape {

        public enum Kind { LIST, SET }
    }

    /** A {@code Map}, by what it is keyed by and what it holds. */
    record Mapping(Type key, Type value) implements PartitionInputShape {}

    /** An {@code Option}, and what it holds when it holds anything. */
    record Optional(Type element) implements PartitionInputShape {}

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

    // --- what the values are, where they are nothing --------------------------------------------

    /**
     * {@code Never}: no value arrives here at all. A fact about the values and not about this
     * compiler — an arm answering {@code unreachable} contributes none, and a position no value
     * reaches is not a position a row could be asked for.
     *
     * <p>Told apart from every case below because those say the shape could not be worked out,
     * whereas this is the shape: there is nothing to divide because there is nothing.
     */
    record Uninhabited() implements Shape {}

    /**
     * {@code Nothing}: the element type of an empty collection, which the position it flows into
     * fixes (ADR-0028). Not yet a value shape and not a failure either — it is a shape a later
     * position decides, so a reader that meets one is early.
     */
    record Bottom() implements Shape {}

    // --- where this compiler could not say what the values are ----------------------------------

    /**
     * The type of something the compiler could not work out. A fact about this compilation: the
     * module carrying it has already been told why, and nothing here may report a second thing
     * about the position on the strength of it.
     */
    record Erroneous() implements Shape {}

    /**
     * A type variable: which type stands here is decided by each application, so the shape is not
     * determined at the point this was asked.
     *
     * <p>Not {@link Unresolved}. Nothing was looked up and failed — there is no name yet to look up.
     */
    record Undecided() implements Shape {}

    /**
     * A name that denotes no declaration this can read, or a newtype whose {@code value} it could
     * not reach — a declaration reachable from itself ends the walk with the name still on.
     *
     * <p>Its own case because the provenance differs from {@link Undecided}: this one was looked up.
     * The interpretation was attempted and did not reach a terminal shape, which is a different
     * thing for a reader to report and a different thing for anyone to fix.
     */
    record Unresolved(TypeSymbol name) implements PartitionInputShape {}
}
