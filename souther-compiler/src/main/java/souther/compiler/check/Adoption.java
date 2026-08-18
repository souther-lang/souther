package souther.compiler.check;

import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Where one reading took a clause in, composed over the clause the way its state is.
 *
 * <p>Two sets and not one. A position a reading took in at one leaf and could not read at another is
 * a position it did not read the clause at: {@code value == 7 || Int.abs(value) >= 2} is read on the
 * left and not on the right, and a set of the leaves that succeeded says the clause was read. The
 * connectives are the clause's, so the same union holds under both of them — an alternative nothing
 * could read leaves the position as open as a conjunct nothing could read does, which is what
 * {@link souther.compiler.values.AdmissibleValues} already says of the values themselves.
 *
 * <p>Composed rather than collected. A set filled as the leaves go by is a fact about the walk and
 * not about the clause, and it cannot be undone by what a later branch failed to read.
 *
 * @param read   the positions a leaf of this clause was taken in at
 * @param missed the positions a leaf of it was about and could not be taken in at
 */
record Adoption(Set<FactSubject> read, Set<FactSubject> missed) {

    private static final Adoption NOTHING = new Adoption(Set.of(), Set.of());

    Adoption {
        read = Set.copyOf(read);
        missed = Set.copyOf(missed);
    }

    /** What a clause this reading has no word for comes to: it took nothing in and missed nothing,
     *  since it was about nothing this reading names. */
    static Adoption nothing() {
        return NOTHING;
    }

    /** A leaf about {@code mentions}, of which this reading took {@code read} in. */
    static Adoption at(Set<FactSubject> mentions, Set<FactSubject> read) {
        Set<FactSubject> missed = new LinkedHashSet<>(mentions);
        missed.removeAll(read);
        Set<FactSubject> took = new LinkedHashSet<>(mentions);
        took.retainAll(read);
        return new Adoption(took, missed);
    }

    /** Both parts of one clause, whichever connective joined them. */
    Adoption and(Adoption other) {
        Set<FactSubject> both = new LinkedHashSet<>(read);
        both.addAll(other.read);
        Set<FactSubject> lost = new LinkedHashSet<>(missed);
        lost.addAll(other.missed);
        return new Adoption(both, lost);
    }

    /** Whether this reading took the whole of what the clause says about {@code position} in. */
    boolean took(FactSubject position) {
        return read.contains(position) && !missed.contains(position);
    }
}
