package souther.compiler.check;

import souther.compiler.types.ResolvedCase;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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
    private final Map<TypeSymbol, Integer> taken = new LinkedHashMap<>();

    private CasePartition(List<TypeSymbol> atoms) {
        subject = new LinkedHashSet<>(atoms);
    }

    /** The atoms to divide, which is what a value of the subject can be. */
    static CasePartition of(List<TypeSymbol> atoms) {
        return new CasePartition(atoms);
    }

    /**
     * Takes the atoms of the arm at {@code index}, and answers where one was already taken.
     *
     * <p>Null where the arm answers for something nothing before it did, which is every arm of a
     * {@code match} that divides its subject. The atoms are taken either way: a caller that refuses
     * an overlap stops there, and one that allows it is asking what is left over all the arms.
     *
     * <p>An arm answering for several cases takes their union, so two of its own alternatives
     * reaching one atom is not an overlap with anything — the arm answers for that value once,
     * however many of its names reach it. Whether writing it that way is worth reporting is a
     * different question and a different reader's ({@link #redundantIn}).
     *
     * <p>The first atom that was already taken and not all of them. What a report needs is one
     * value the two arms both answer for; listing every shared value says the same thing at
     * whatever length the declaration happens to have.
     */
    Overlap take(List<TypeSymbol> arm, int index) {
        Overlap found = null;
        for (TypeSymbol atom : new LinkedHashSet<>(arm)) {
            Integer earlier = taken.putIfAbsent(atom, index);
            if (earlier != null && found == null) {
                found = new Overlap(atom, earlier, index);
            }
        }
        return found;
    }

    /** One value two arms both answer for, and which arms they are. */
    record Overlap(TypeSymbol value, int earlier, int here) {}

    /**
     * An alternative naming a case an earlier alternative of the same arm already named.
     *
     * <p>Null where each names a different case. Asked apart from {@link #redundantIn} and before
     * it, because the two are different findings and the more specific one is the one worth saying:
     * a name written twice is a slip, and a name covered by another is usually the case the author
     * meant not being the case they named. Folded into one walk, which of the two an author is told
     * would follow from whichever pair the walk reached first — so
     * {@code | Station | OnceKind | Station} would report the covering and never mention that
     * {@code Station} is there twice.
     *
     * <p>By case and not by spelling. Two alternatives are the same one when they name one type;
     * what each was written as is how it is reported and not what it is.
     */
    static Duplicate namedTwiceIn(List<ResolvedCase> alternatives) {
        Map<TypeSymbol, Integer> first = new LinkedHashMap<>();
        for (int here = 0; here < alternatives.size(); here++) {
            Integer before = first.putIfAbsent(alternatives.get(here).name(), here);
            if (before != null) {
                return new Duplicate(here, before);
            }
        }
        return null;
    }

    /** An alternative naming a case already named, and where it was named first. */
    record Duplicate(int again, int first) {}

    /**
     * An alternative of one arm that answers for nothing another of them answers for too.
     *
     * <p>Null where each alternative adds something. What makes one redundant is inclusion and not
     * spelling: {@code | Station | OnceKind} answers for a station under either name, and so does
     * {@code | Station | Station}. Held because an arm is a list of what it answers for, and an
     * entry that adds nothing to that list is a line the author wrote for a reason that did not
     * happen — most often the case they meant is not the one they named.
     *
     * <p>Where two alternatives answer for exactly the same values, the later one is the redundant
     * one: the arm reads left to right, and the first is where the reader learns what it answers
     * for.
     *
     * <p>An alternative naming a case another named is one of those, and is {@link #namedTwiceIn}'s
     * to report. This is asked after it, so what comes back here is always a pair of different
     * cases.
     */
    static Redundant redundantIn(List<ResolvedCase> alternatives) {
        for (int here = 0; here < alternatives.size(); here++) {
            Set<TypeSymbol> mine = new LinkedHashSet<>(alternatives.get(here).atoms());
            for (int other = 0; other < alternatives.size(); other++) {
                if (other == here) {
                    continue;
                }
                Set<TypeSymbol> theirs = new LinkedHashSet<>(alternatives.get(other).atoms());
                // An equal pair is reported at the later of the two, so `other` may only be the
                // earlier one when the two answer alike.
                boolean covered = theirs.containsAll(mine)
                        && (!mine.containsAll(theirs) || other < here);
                if (covered) {
                    return new Redundant(here, other);
                }
            }
        }
        return null;
    }

    /**
     * An alternative that adds nothing, and the one that covers it.
     *
     * <p>Covers and not answered-first. The inclusion is looked for in both directions, so where
     * one alternative is strictly inside another the covering one may be written after it —
     * {@code | Station | OnceKind} is reported at {@code Station} with {@code OnceKind} as what
     * covers it. Only a pair answering alike is settled by which came first, and there the earlier
     * one is the covering one.
     */
    record Redundant(int adds, int covering) {}

    /** The atoms no arm answered for, in the order the subject states them. */
    List<TypeSymbol> unanswered() {
        List<TypeSymbol> left = new ArrayList<>();
        for (TypeSymbol atom : subject) {
            if (!taken.containsKey(atom)) {
                left.add(atom);
            }
        }
        return left;
    }
}
