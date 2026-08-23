package souther.compiler.check;

import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * The atoms a subject can be, divided among the arms that answer for them.
 *
 * <p>A set operation and nothing more. Which arm of a {@code match} takes a value is decided by the
 * order the arms are written, and whether two arms may answer for one value at all is a policy —
 * a {@code match} partitions, a declared relation does not (its rules are a conjunction, and
 * {@code ContractDischarge} counts what no rule reaches). Neither is decided here. What is here is
 * what those readers disagreed about while each worked it out for itself: which atoms are left, and
 * which an arm shares with one that came before it.
 *
 * <p>Kept out of {@link CaseSpace} deliberately. That answers what a subject can be selected as, and
 * a subject has no opinion on whether the arms written over it divide it up.
 *
 * <p>Order is the subject's throughout. What is left comes back in the order the subject states its
 * atoms, so a report of an unanswered case reads in the order the model declares them.
 */
final class CasePartition {

    private final Set<TypeSymbol> subject;
    private final Set<TypeSymbol> taken = new LinkedHashSet<>();

    private CasePartition(List<TypeSymbol> atoms) {
        subject = new LinkedHashSet<>(atoms);
    }

    /** The atoms to divide, which is what a value of the subject can be. */
    static CasePartition of(List<TypeSymbol> atoms) {
        return new CasePartition(atoms);
    }

    /**
     * Takes {@code arm}'s atoms, and answers those an earlier arm had already taken.
     *
     * <p>Empty where the arm answers for something nothing before it did — which is every arm of a
     * {@code match} that divides its subject. The atoms are taken either way: a caller that refuses
     * an overlap stops, and one that allows it is asking what is left over all the arms.
     *
     * <p>An arm answering for several cases takes their union. Two of its own alternatives reaching
     * one atom is not an overlap with anything: the arm answers for that value once, however many
     * of its names reach it.
     */
    List<TypeSymbol> take(List<TypeSymbol> arm) {
        List<TypeSymbol> already = new ArrayList<>();
        // The arm's own atoms first, so two of its alternatives reaching one atom is one answer and
        // not this arm overlapping itself.
        for (TypeSymbol atom : new LinkedHashSet<>(arm)) {
            if (!taken.add(atom)) {
                already.add(atom);
            }
        }
        return already;
    }

    /** The atoms no arm answered for, in the order the subject states them. */
    List<TypeSymbol> unanswered() {
        List<TypeSymbol> left = new ArrayList<>();
        for (TypeSymbol atom : subject) {
            if (!taken.contains(atom)) {
                left.add(atom);
            }
        }
        return left;
    }
}
