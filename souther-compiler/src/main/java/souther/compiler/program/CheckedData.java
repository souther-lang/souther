package souther.compiler.program;

import souther.compiler.core.ValueShape;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.NoSuchElementException;

/**
 * What one of a module's declared data is made of, as an output outside this compiler reads it.
 *
 * <p>A {@link Type.Ref} names a data and says nothing of what is in it. So a reader holding a value
 * of a declared type could say neither where in it a field lies nor which case it turned out to be,
 * and both are decisions the language made. This is where they are read back.
 *
 * <p>The shape a value has, and not the declaration as it was written. An include is already
 * flattened into {@link Product#fields()}, and a case that is itself a sum is already descended
 * into {@link Sum#cases()}. Either one worked out again by a reader would be a second answer to a
 * question the language settled once, and two readers that each descended would differ at the
 * shape neither of them is written against: the one where the descent reaches a case twice.
 *
 * <p>Three arms and not fields-or-cases. The language declares in three forms, and a unit written as
 * a product with no fields is a declaration a reader cannot tell from one that happens to have
 * none — while {@link souther.compiler.core.Core.UnitValue} names exactly the first.
 *
 * <p>Only what a module declares. What the language gives — a primitive standing as a case,
 * {@code Option}'s cases — is declared by no module, which is why every arm is named by a
 * {@link TypeSymbol.AtModule} rather than by a {@link TypeSymbol}. A name that is not one, among
 * them what {@code Core.UnitValue} can carry, names something no module declared; it is not a
 * declaration this snapshot is missing.
 *
 * <p>{@link Product} is a class and answers no {@code equals}. What a value of a product is made
 * of is {@link ValueShape}, which the check answers and this hands over whole — the fields, the
 * binding each is read through, and what must hold of a value built from them. {@link Sum} and
 * {@link Unit} hold everything they will hold, so they are records.
 */
public sealed interface CheckedData {

    /** Which declaration this is. */
    TypeSymbol.AtModule name();

    /**
     * A data a value is built out of, field by field.
     *
     * <p>A {@code newtype} is one of these: a single field called {@code value} holding what it
     * wraps (spec §newtype). Only its external representation differs, which is
     * {@code check.Boundary}'s answer and no part of what a value is made of, so nothing here marks
     * it out.
     */
    final class Product implements CheckedData {

        private final ValueShape shape;

        Product(ValueShape shape) {
            if (shape == null) {
                throw new IllegalArgumentException("a declared data is named");
            }
            this.shape = shape;
        }

        @Override
        public TypeSymbol.AtModule name() {
            return shape.name();
        }

        /**
         * Every field a value of this holds, in the order they are laid out. What an included data
         * brought in is already among them, and comes first.
         *
         * <p>This is the layout and not a way of pairing a construction off against it.
         * {@link souther.compiler.core.Core.Construct} supplies every one of these and names each
         * by the field it fills, so what a reader has to know is where a name lies —
         * {@link #positionOf} — rather than which value happens to stand at which index. The two
         * orders do agree, and that agreement is a property of the checked program worth holding
         * to; a reader that placed by it would be reading a position as an identity.
         *
         * <p>Each field carries the binding a clause reads it through, which is what makes
         * {@link #invariants()} runnable: an output putting a value under that binding and emitting
         * the clause is running what the checker decided, and one working the bindings out from the
         * declarations would be deciding it a second time.
         */
        public List<ValueShape.Field> fields() {
            return shape.fields();
        }

        /**
         * What must hold of a value of this, in the order a failure is decided in.
         *
         * <p>The clauses that apply and not the ones this declaration wrote: an include carries the
         * clauses of what it takes in, and a value of this is held to those as much as to its own.
         * Each is the condition as the checker elaborated it, over the bindings {@link #fields()}
         * names — the same one the JVM's {@code __construct} refuses a value by.
         *
         * <p>Empty where nothing is stated, which is a data any value of its fields is one of.
         */
        public List<ValueShape.Invariant> invariants() {
            return shape.invariants();
        }

        /**
         * Where the field called {@code field} lies among {@link #fields()}.
         *
         * @throws NoSuchElementException where this data has no such field — a name that is not a
         *     field of it is a mistake at the reader, and answering with a position that is not one
         *     would put the mistake in whatever it emitted
         */
        public int positionOf(String field) {
            return shape.positionOf(field);
        }

        @Override
        public String toString() {
            return shape.name().toString();
        }
    }

    /**
     * The cases a value of this can be (spec §sum-data).
     *
     * <p>What it can be, which is not what it lists. A sum whose case is a sum is transparent as a
     * value — anything of the inner one is of the outer one — so the descent is made here and what
     * is answered is the cases that are not themselves sums. A case reached by two paths is one
     * case.
     *
     * <p>The order is deterministic: the order the cases are written in, a case keeping the place
     * it was first reached at. A case is identified by its {@link TypeSymbol}, and its position
     * here is not that identity. One data may be a case of two sums declared in one module and
     * stands at a different position in each, so a reader that made a position into a tag would
     * have given one value two of them.
     */
    record Sum(TypeSymbol.AtModule name, List<TypeSymbol> cases) implements CheckedData {

        public Sum {
            if (name == null) {
                throw new IllegalArgumentException("a declared data is named");
            }
            cases = List.copyOf(cases);
        }
    }

    /** One value, and naming it is that value (spec §unit-data). What {@code Core.UnitValue}
     *  names. */
    record Unit(TypeSymbol.AtModule name) implements CheckedData {

        public Unit {
            if (name == null) {
                throw new IllegalArgumentException("a declared data is named");
            }
        }
    }
}
