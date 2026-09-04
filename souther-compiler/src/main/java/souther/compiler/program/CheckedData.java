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
 * of a declared type could say neither where in it a field lies, nor which case it turned out to
 * be, nor which of the language's forms it was declared in, and all three are decisions the
 * language made. This is where they are read back.
 *
 * <p>What the checker settled and a reader cannot recover from a name: the form a data was declared
 * in, the shape a value of it has, and the cases it can be.
 *
 * <p>The shape and not the declaration as it was written. An include is already flattened into
 * {@link WithFields#fields()}, and a case that is itself a sum is already descended
 * into {@link Sum#cases()}. Either one worked out again by a reader would be a second answer to a
 * question the language settled once, and two readers that each descended would differ at the
 * shape neither of them is written against: the one where the descent reaches a case twice.
 *
 * <p>Four arms, one to a form the language declares in, and not fields-or-cases. Which form a
 * declaration was written in is the one thing here its shape does not answer, and a reader given
 * the shape alone would be left to guess it from the name of a member. {@code data X = Y} and
 * {@code data X = { value: Y }} are made of one field of the same type and hold the same clauses.
 * At a position declaring the first, a value is written as {@code Y} is written; at one declaring
 * the second, as an object. Which of the two a declaration is, is decided by the syntax it was
 * written in rather than by the shape it came out as (spec §newtype). A {@link Unit} is its own arm
 * for the same reason: a product that happens to have no fields is a declaration a reader could not
 * tell it from, while {@link souther.compiler.core.Core.UnitValue} names exactly the first.
 *
 * <p>What was declared, by a module of this compilation or by the language in the reserved
 * namespace. The two are one kind of thing here, and which of them declared a given one is
 * {@link DeclaredBy}, answered where a reader asks what an identity is a declaration of.
 *
 * <p>What is outside is what nothing declares. A primitive standing as a case and {@code Option}'s
 * cases are given by the language directly, with no declaration behind them, which is why every arm
 * is named by a {@link TypeSymbol.AtModule} rather than by a {@link TypeSymbol}. A name that is not
 * one, among them what {@code Core.UnitValue} can carry, is answered for by the sealed identity
 * itself; it is not a declaration this snapshot is missing.
 *
 * <p>{@link Product} and {@link Newtype} are classes and answer no {@code equals}. What a value of
 * either is made of is {@link ValueShape}, which the check answers and this hands over whole — the
 * fields, the binding each is read through, and what must hold of a value built from them.
 * {@link Sum} and {@link Unit} hold everything they will hold, so they are records.
 */
public sealed interface CheckedData {

    /** Which declaration this is. */
    TypeSymbol.AtModule name();

    /**
     * A data a value is built out of, field by field: a {@link Product} and a {@link Newtype}.
     *
     * <p>The second question asked of a declaration here, and the one the arms do not answer. Which
     * form it was written in decides how a value of it crosses; what a value is built out of, and
     * where in it a field lies, is this — and a newtype answers it exactly as the one-field product
     * it is made like, because construction, access and the clauses that must hold are the same for
     * the two (spec §newtype).
     *
     * <p>Two questions and two ways of being total. A reader laying a value out asks here and is
     * answered for every declaration without naming a form; a reader writing a value's external
     * form asks the arm and has to say what it writes for each. Carried on one hierarchy, the
     * second reader would be asking about layout, which answers alike for the two — and answering
     * alike is what this is for.
     */
    sealed interface WithFields permits Product, Newtype {

        /** Which declaration this is. */
        TypeSymbol.AtModule name();

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
        List<ValueShape.Field> fields();

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
        List<ValueShape.Invariant> invariants();

        /**
         * Where the field called {@code field} lies among {@link #fields()}.
         *
         * @throws NoSuchElementException where this data has no such field — a name that is not a
         *     field of it is a mistake at the reader, and answering with a position that is not one
         *     would put the mistake in whatever it emitted
         */
        int positionOf(String field);
    }

    /** A data declared with its fields written out, {@code data X = { ... }} (spec §product-data).
     *  At a boundary position that declares this type, a value of one crosses as an object whatever
     *  it holds — a single member included (spec §newtype). */
    final class Product implements CheckedData, WithFields {

        private final ValueShape shape;

        Product(ValueShape shape) {
            if (shape == null) {
                throw new IllegalArgumentException(
                        "a product is what a value of it is made of and what must hold of one");
            }
            this.shape = shape;
        }

        @Override
        public TypeSymbol.AtModule name() {
            return shape.name();
        }

        @Override
        public List<ValueShape.Field> fields() {
            return shape.fields();
        }

        @Override
        public List<ValueShape.Invariant> invariants() {
            return shape.invariants();
        }

        @Override
        public int positionOf(String field) {
            return shape.positionOf(field);
        }

        @Override
        public String toString() {
            return shape.name().toString();
        }
    }

    /**
     * A data declared over another, {@code data X = Y} (spec §newtype).
     *
     * <p>One value under another name. At a boundary position that declares this type, a value of
     * it is written as a value of {@link #wrapped()} is written — bare, and not as an object
     * holding it under a key — and that is the whole of the difference from a product declared with
     * a single member, which is why everything else about it is asked through {@link WithFields}.
     *
     * <p>The position it stands at is the other half of a representation, and it is not this
     * (ADR-0094). A sum that admits this as a case writes what admitting it adds: a bare scalar has
     * nowhere to carry the discriminator, so the payload stands under a {@code value} key there
     * (ADR-0014, spec §sum-discrimination). What is here is what this declaration is, and a reader
     * writing a value asks it together with the position the value is being written at.
     */
    final class Newtype implements CheckedData, WithFields {

        private final ValueShape shape;

        Newtype(ValueShape shape) {
            if (shape == null) {
                throw new IllegalArgumentException(
                        "a newtype is what a value of it is made of and what must hold of one");
            }
            if (shape.fields().size() != 1) {
                throw new IllegalArgumentException("a newtype is one value under another name, and `"
                        + shape.name() + "` is made of " + shape.fields());
            }
            this.shape = shape;
        }

        @Override
        public TypeSymbol.AtModule name() {
            return shape.name();
        }

        /**
         * The type this is a name for — the {@code Y} of {@code data X = Y}.
         *
         * <p>The type and not the field that holds it. The field is the one the desugaring wrote to
         * hold the value, under a name that pass chose; handed the field, a reader would be reading
         * a name this compiler picked as though the declaration had written it — and reading a
         * member's name for what a value is written as is the reading this arm is here to spare it.
         */
        public Type wrapped() {
            return shape.fields().getFirst().type();
        }

        @Override
        public List<ValueShape.Field> fields() {
            return shape.fields();
        }

        @Override
        public List<ValueShape.Invariant> invariants() {
            return shape.invariants();
        }

        @Override
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
