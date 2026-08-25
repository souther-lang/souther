package souther.compiler.core;

import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.NoSuchElementException;
import java.util.Optional;

/**
 * What a value built field by field is made of, and what must hold of one.
 *
 * <p>Both halves of one environment. A clause reads a field by its binding and whoever runs the
 * clause has to put the field's value under that binding, so the fields and the conditions are one
 * answer: two readers given them apart would each work out where a field is read through, and the
 * day their two walks disagreed the condition would be run over a value it was not written about.
 *
 * <p>A condition is the checker's ({@link Invariant#condition()}), as a body is. What decides what
 * a clause means is the elaboration, and a reader elaborating one of its own would be the second
 * place that decided it — which is what {@code Core} was made to end.
 *
 * <p>The shape of the data a value is being built as, and not of the declaration a clause was
 * written on. An include carries a clause into the data that includes it (spec §invariant), and it
 * is checked there, over the fields that data has; the binding it reads is the one the declaration
 * that wrote it gave, which is why the fields carry theirs rather than being numbered here.
 */
public record ValueShape(TypeSymbol.AtModule name, List<Field> fields, List<Invariant> invariants) {

    public ValueShape {
        if (name == null) {
            throw new IllegalArgumentException("a declared data is named");
        }
        fields = List.copyOf(fields);
        invariants = List.copyOf(invariants);
    }

    /**
     * One field: what it is called, what is in it, and the binding a clause reads it through.
     *
     * @param binding what a clause naming this field resolved to — the binding of the declaration
     *     that wrote the field, which is the declaration whose clause reads it
     */
    public record Field(String name, Type type, BindingId binding) {

        public Field {
            if (name == null || type == null || binding == null) {
                throw new IllegalArgumentException("a field is a name, what is in it, and what a"
                        + " clause reads it through: " + name + " " + type + " " + binding);
            }
        }

        @Override
        public String toString() {
            return name + ": " + Type.show(type);
        }
    }

    /**
     * One clause: the name a failure is reported under, and what has to hold.
     *
     * <p>Unnamed where the author wrote no name. What is reported then is the declaration and the
     * clause's place in {@link ValueShape#invariants()}, which is the order a failure is decided in.
     */
    public record Invariant(Optional<String> name, Core condition) {

        public Invariant {
            if (condition == null) {
                throw new IllegalArgumentException("a clause is something that has to hold");
            }
        }
    }

    /**
     * Where the field called {@code field} lies among {@link #fields()}.
     *
     * <p>The one derivation of a position from a name, so that a reader emitting a load and a reader
     * emitting a store cannot come to place the same field differently.
     *
     * @throws NoSuchElementException where this data has no such field — a name that is not a field
     *     of it is a mistake at the reader, and answering with a position that is not one would put
     *     the mistake in whatever it emitted
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
