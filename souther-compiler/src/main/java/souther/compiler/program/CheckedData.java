package souther.compiler.program;

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
 * question this compiler settled once — and the descent in particular is a question four readers
 * inside the compiler used to answer for themselves, disagreeing wherever it reached one case
 * twice.
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
 * <p>{@link Product} and {@link Field} are classes and answer no {@code equals}. What a product is
 * known to be will grow — its invariant clauses, and the binding each field is read through — and a
 * record would fix both the constructor and what two of them are compared by before there is a
 * reader for either. {@link Sum} and {@link Unit} hold everything they will hold, so they are
 * records.
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

        private final TypeSymbol.AtModule name;
        private final List<Field> fields;

        Product(TypeSymbol.AtModule name, List<Field> fields) {
            if (name == null) {
                throw new IllegalArgumentException("a declared data is named");
            }
            this.name = name;
            this.fields = List.copyOf(fields);
        }

        @Override
        public TypeSymbol.AtModule name() {
            return name;
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
         */
        public List<Field> fields() {
            return fields;
        }

        /**
         * Where the field called {@code field} lies among {@link #fields()}.
         *
         * <p>The one derivation of a position from a name, so that a reader emitting a load and a
         * reader emitting a store cannot come to place the same field differently. Derived rather
         * than held: a map beside the list would be the same fact twice, and the two would agree
         * until one of them was rebuilt.
         *
         * @throws NoSuchElementException where this data has no such field — a name that is not a
         *     field of it is a mistake at the reader, and answering with a position that is not one
         *     would put the mistake in whatever it emitted
         */
        public int positionOf(String field) {
            for (int i = 0; i < fields.size(); i++) {
                if (fields.get(i).name().equals(field)) {
                    return i;
                }
            }
            throw new NoSuchElementException("`" + name + "` has no field `" + field + "`");
        }

        @Override
        public String toString() {
            return name.toString();
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

    /** One field: what it is called, and what is in it. */
    final class Field {

        private final String name;
        private final Type type;

        Field(String name, Type type) {
            if (name == null || type == null) {
                throw new IllegalArgumentException("a field is a name and what is in it: "
                        + name + " " + type);
            }
            this.name = name;
            this.type = type;
        }

        /** What the field is called — what a construction fills and a field access names. */
        public String name() {
            return name;
        }

        /** What is in it. */
        public Type type() {
            return type;
        }

        @Override
        public String toString() {
            return name + ": " + Type.show(type);
        }
    }
}
