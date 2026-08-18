package souther.compiler.check;

import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Where one reading took a clause in, composed over the clause the way its state is.
 *
 * <p>The same algebra {@link souther.compiler.values.AdmissibleValues} composes its values by, and
 * it has to be: what a reading may say about a position and where it took the clause in are two
 * projections of one reading, and a rule that widens the first without widening the second is a
 * position reported as read on evidence the reading itself does not have.
 *
 * <p>So the connectives are not one operation. Under a conjunction, a part nothing could read
 * leaves the parts beside it saying what they said — {@code value >= 1 && f(value)} still bounds the
 * value. Under a choice it does not: a value satisfying the branch nothing could read is under no
 * obligation from the other, so {@code x == 7 || f(y)} says nothing about {@code x} either. That is
 * why {@link #dropped} is here and why {@link #either} spoils across positions the unread branch
 * never named — the same reason {@code AdmissibleValues.join} does.
 *
 * <p>What is recorded is that the reading settled what the clause does to a position, which is not
 * the same as its having narrowed anything there. A branch shown to admit nothing settles every
 * position it named: the choice is the other branch, so what this clause does to a position only
 * that branch spoke of is nothing at all — an answer, and one only a reading that got to the end of
 * the branch could give.
 *
 * <p>Composed rather than collected. A set filled as the leaves go by is a fact about the walk and
 * not about the clause, and it cannot be undone by what a later branch failed to read.
 *
 * @param read    the positions a part of this clause was taken in at
 * @param missed  the positions a part of it was about, or was widened by a part nothing read, and
 *                so was not taken in at
 * @param dropped whether a part of this clause went unread anywhere in it, which is what a choice
 *                needs in order to know that a branch widened it. What that part was about is not
 *                carried: a branch nothing could read widens the positions the other branch spoke
 *                about whether or not it names them
 */
record Adoption(Set<FactSubject> read, Set<FactSubject> missed, boolean dropped) {

    private static final Adoption NOTHING = new Adoption(Set.of(), Set.of(), false);

    Adoption {
        read = Set.copyOf(read);
        missed = Set.copyOf(missed);
    }

    /** What a clause this reading has no word for comes to. */
    static Adoption nothing() {
        return NOTHING;
    }

    /**
     * One leaf: what it was about, what this reading produced of it, and whether it gave up on it.
     *
     * <p>{@code failed} is the reading's own, and not the emptiness of what it produced: a leaf
     * about no position of this value produces nothing and is not a leaf a reading gave up on —
     * though a reading that has no word for it did give up, which is what each of them says for
     * itself.
     */
    static Adoption at(Set<FactSubject> mentions, Set<FactSubject> produced, boolean failed) {
        Set<FactSubject> missed = new LinkedHashSet<>(mentions);
        missed.removeAll(produced);
        Set<FactSubject> took = new LinkedHashSet<>(mentions);
        took.retainAll(produced);
        return new Adoption(took, missed, failed);
    }

    /**
     * Both parts holding at once.
     *
     * <p>Nothing spoils anything: a part nothing read leaves the parts beside it saying what they
     * said, since all of them hold.
     */
    Adoption both(Adoption other) {
        return new Adoption(union(read, other.read), union(missed, other.missed),
                dropped || other.dropped);
    }

    /**
     * Either part holding.
     *
     * <p>A branch nothing could read widens every position the other branch spoke about, named
     * there or not: a value satisfying the unread branch owes the read one nothing. Read as a union
     * of what the branches managed, {@code x == 7 || f(y)} said {@code x} had been read — and what
     * the clause leaves {@code x} is exactly what nothing here can say.
     */
    Adoption either(Adoption other) {
        Set<FactSubject> lost = union(missed, other.missed);
        if (other.dropped) {
            lost = union(lost, read);
        }
        if (dropped) {
            lost = union(lost, other.read);
        }
        return new Adoption(union(read, other.read), lost, dropped || other.dropped);
    }

    /** Whether this reading settled what the whole of the clause does to {@code position}. */
    boolean took(FactSubject position) {
        return read.contains(position) && !missed.contains(position);
    }

    /** The positions any part of the clause was about. */
    Set<FactSubject> mentions() {
        return union(read, missed);
    }

    /**
     * This branch of a choice, beside one shown to admit nothing.
     *
     * <p>The dead branch settles the positions it named: nothing satisfies it, so what the choice
     * does to a position only it spoke of is nothing, which is an answer. Its own misses do not
     * come with it — a rule it could not read is a rule about a branch nobody can take — and
     * neither does its {@link #dropped}, for the same reason.
     *
     * <p>What this branch missed still wins. {@code (s < "") || f(x)} leaves {@code x} open however
     * dead the first branch is, so the surviving branch's account is the one that outranks.
     */
    Adoption beside(Adoption dead) {
        return new Adoption(union(read, dead.mentions()), missed, dropped);
    }

    /**
     * Two branches of a choice, both shown to admit nothing.
     *
     * <p>Then the choice admits nothing, which settles every position either of them named: the
     * values there are exactly none. No branch is left to have missed anything.
     */
    Adoption bothDead(Adoption other) {
        return new Adoption(union(mentions(), other.mentions()), Set.of(), false);
    }

    private static Set<FactSubject> union(Set<FactSubject> these, Set<FactSubject> those) {
        if (those.isEmpty()) {
            return these;
        }
        Set<FactSubject> out = new LinkedHashSet<>(these);
        out.addAll(those);
        return out;
    }
}
