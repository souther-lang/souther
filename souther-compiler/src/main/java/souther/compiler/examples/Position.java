package souther.compiler.examples;

import souther.compiler.ast.Hir;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;

/**
 * What reads the value written at one place in a fixture.
 *
 * <p>A neutral form is the case's own form plus whatever the type reading it there asks to be written
 * beside it: a discriminator where that type is a sum, the bare name where it is an enumeration, the
 * {@code "value"} envelope where a newtype is read through a sum (spec §sum-discrimination). So the
 * form is a question about the place a value stands and not about the value, and this is what the
 * place answers with.
 *
 * <p>{@link Unread} is the other answer and is one of the two rather than the absence of one. A
 * behavior answering with several types has no one decoder, so what stands in for it is admitted by
 * being one of the cases and read by nothing ({@code FixtureReader}); a field no declaration names
 * says nothing about what it holds. Neither is a place where some other type reads the case, so
 * neither asks for anything to be written beside it. Nothing is inferred there — in particular not
 * from the sums that happen to list the case, which says where the case may be read rather than
 * where it is, and moves when a sum nothing here reads the value through is declared elsewhere.
 *
 * <p>Written as a type so that a reader deciding a form has to say which of the two it has. The same
 * state carried as a null {@code Type} was re-read at each method that took one, and that is where a
 * search over every visible sum got in.
 *
 * <p>{@link Unread} says there is no reader, and says nothing about a type. It is not a type that is
 * unknown, not one still to be worked out, and not one this cannot read: those are answers about a
 * type, and each has somewhere of its own to be answered — what a fixture may be built through is
 * {@link FixtureShape}'s, and a whole answer that is several types is a shape that does not exist
 * rather than a place nothing reads. Widening this to hold any of them would put back the state the
 * null {@code Type} was, under a better name.
 */
sealed interface Position {

    /** Read through {@code type}, which is what asks for what is written beside the case. */
    record At(Type type) implements Position {

        public At {
            if (type == null) {
                throw new IllegalArgumentException("a position that reads a value has a type;"
                        + " Position.UNREAD is the one that does not");
            }
        }
    }

    /** Nothing reads the value here, so nothing is written beside it. */
    record Unread() implements Position {}

    Position UNREAD = new Unread();

    /** Read through {@code type}. */
    static Position at(Type type) {
        return new At(type);
    }

    /**
     * Read through what a declaration writes at this place, and {@link #UNREAD} where no declaration
     * names it — a field a fixture wrote that the data does not declare, or a newtype's base where
     * the type it wraps has no written form.
     */
    static Position declaredBy(Hir.TypeRef declared) {
        return declared == null ? UNREAD : at(declared.denotes());
    }

    /** The place a value stands at where an optional makes room for it: writing a value for a `T?`
     *  field writes a `T`, so the optional is opened before the form is asked for. */
    default Position opened() {
        return this instanceof At(Type type) && type instanceof Type.OptionOf o
                ? at(o.element()).opened()
                : this;
    }

    /** Where a written list's elements stand: a list's or a set's element, or a map's entry pair. */
    default Position element() {
        if (!(opened() instanceof At(Type type))) {
            return UNREAD;
        }
        return switch (type) {
            case Type.ListOf l -> at(l.element());
            case Type.SetOf s -> at(s.element());
            case Type.MapOf m -> at(Type.tuple(List.of(m.key(), m.value())));
            default -> UNREAD;
        };
    }

    /** Where the parts of a written tuple of {@code arity} stand. A map's entry is the pair carrying
     *  its key type, which is where an enumeration key is written. Always {@code arity} places, so a
     *  tuple written where nothing says what it holds is read part by part like any other. */
    default List<Position> parts(int arity) {
        List<Type> types = !(opened() instanceof At(Type type)) ? null : switch (type) {
            case Type.MapOf m when arity == 2 -> List.of(m.key(), m.value());
            case Type.TupleOf t when t.elements().size() == arity -> t.elements();
            default -> null;
        };
        List<Position> out = new ArrayList<>(arity);
        for (int i = 0; i < arity; i++) {
            out.add(types == null ? UNREAD : at(types.get(i)));
        }
        return List.copyOf(out);
    }
}
