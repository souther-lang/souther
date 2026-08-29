package souther.compiler.partition;

import souther.compiler.inputs.Membership;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.TypeSymbol;

import java.util.List;

/**
 * Whether a value an {@code example} row was given belongs to one equivalence class.
 *
 * <p>Separate from being able to produce a value of that class. A class can be recognised in rows the
 * author already wrote while nothing can generate a representative for it — a type whose invariant is
 * a pattern, a record whose fields constrain each other — and treating those as unmeasurable would
 * throw away coverage that is already there.
 *
 * <p>The answer is a {@link Membership} and not a {@code boolean} because a classifier may have to
 * read the value before it can say anything about it, and reading can fail. What did the reading
 * says why it failed; nothing downstream is in a position to work it out.
 *
 * <p><b>A way of asking, and never what a class is.</b> What a class means is a {@link Recognition},
 * which is a value; one of these is made from one of those by {@link Recognitions#reading}, wherever
 * something is about to read a row. Nothing builds one any other way — a class whose meaning existed
 * only inside a function it had been handed could not be compared with another class and could not
 * be kept in an answer.
 */
@FunctionalInterface
public interface Classifier {

    Membership membershipOf(ObservedValue value);

    /**
     * The value under {@code worn}: a newtype is observed as its construction, whose one field is
     * {@code value} (spec §data).
     *
     * <p>The one place an observation has names taken off it. What a row wrote is what arrives, and
     * every reader that walks into one — a class asking which case it is, a walk on its way to a
     * field under it — takes them off the same way and by name, so that a record whose own field is
     * called {@code value} is never mistaken for a name worn over one.
     */
    static ObservedValue inside(List<TypeSymbol> worn, ObservedValue value) {
        ObservedValue at = value;
        for (TypeSymbol name : worn) {
            if (!(at instanceof ObservedValue.Constructed constructed)
                    || !name.equals(constructed.type())) {
                return at;
            }
            ObservedValue held = constructed.field("value");
            if (held == null) {
                // The construction is there and what it holds is not, which is what an observation
                // stopped one layer down leaves. Handed on as it stands: why there is no value is
                // the observation's to say and not something to be read off the outside of it.
                return at;
            }
            at = held;
        }
        return at;
    }
}
