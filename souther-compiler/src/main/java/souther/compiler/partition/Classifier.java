package souther.compiler.partition;

import souther.compiler.inputs.Membership;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.function.Predicate;

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
 */
@FunctionalInterface
public interface Classifier {

    Membership membershipOf(ObservedValue value);

    /**
     * One that answers by looking at the value it is given.
     *
     * <p>For the classes told apart by shape — a case of a sum, a {@code Bool}, whether an optional
     * holds anything — where the value at the position is the value to look at. An observation that
     * did not arrive is answered before the predicate is asked, because that is a fact about the
     * observation rather than a thing the class declines.
     */
    static Classifier byShape(Predicate<ObservedValue> holds) {
        return value -> {
            Membership.Incomplete unread = Membership.unread(value);
            return unread != null ? unread : Membership.of(holds.test(value));
        };
    }

    /** Recognises nothing: a class that exists but cannot be told from another by looking. */
    static Classifier none() {
        return _ -> Membership.NO_MATCH;
    }

    /**
     * One that reads the value inside the names the position writes it under.
     *
     * <p>The other direction of the same fact a representative is written by. A position declaring
     * {@code data StageN = Stage} divides into the cases of {@code Stage}, a row writes
     * {@code StageN(Prospecting)}, and what arrives is the construction with the case one inside
     * it. A class asking what case it is has to be asked of the case.
     *
     * <p>Only the names that are there come off. A value that is not wearing them is handed to
     * {@code inner} as it stands, which answers for it — the alternative is deciding here that a
     * value belongs to no class, which is a judgement the classes make.
     *
     * @param worn the names, outermost first, as {@code TypeView} reads them off the position
     */
    static Classifier under(List<TypeSymbol> worn, Classifier inner) {
        if (worn.isEmpty()) {
            return inner;
        }
        return value -> inner.membershipOf(inside(worn, value));
    }

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
