package souther.compiler.check;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * Which readings took each clause into their own semantics.
 *
 * <p>Recorded where each reading runs, and by that reading. A caller working out from a clause's
 * spelling which reading ought to have managed it is guessing at another reader's semantics — which
 * is the defect this exists to stop, one level over from the one it was written for: an ordering
 * bound is unreadable to the reading that turns clauses into sets of values and is read whole by two
 * others, and the shape says nothing about which of them managed it.
 *
 * <p>Per clause, because that is the granularity a question has. Asked per position, one clause's
 * failure is the account of every clause beside it: {@code invariant floor = value >= 1} leaves the
 * reading of values short at a position, and {@code invariant seven = value == 7} written beside it
 * was taken in whole and came back reported as unread.
 *
 * <p>Filed under {@link RuleRef} and not under the clause reference the walk had in hand. Every
 * clause reaching here is an invariant's, so the two would key the same map today — and the value
 * recorded here is carried to a report, where what names a rule is the rule. Weakened on the way
 * out, each reader downstream had to work the identity back out for itself (issue #852).
 *
 * <p>Success and not attempt. A reading that recognised part of a clause and gave up took nothing
 * in, so nothing here records it — what is written down is the point at which a reading adopted the
 * clause into what it holds.
 *
 * <p>Every part of the clause, and not one of them. A conjunction is one rule the author wrote and
 * is read one conjunct at a time; a clause half of which nothing took in is a clause nothing took
 * in, and answering it on the strength of the half that was read is how {@code value >= 1 &&
 * value * value >= 4} came back with nothing to say while the same two rules written apart were
 * reported. The same reading {@code Predicates.Owed.and} makes of a clause it could not read all
 * of.
 *
 * <p><b>Every reading, and each one asked at its own adoption point.</b> There are more of them than
 * a reader notices: {@code value * 2 >= 4} is beyond the reading of ends and beyond the reading of
 * values, and the reading that builds the numeric constraints takes it in whole. An accounting that
 * consulted two of the three would report that clause exactly the way #842 reports a bound — as a
 * rule this compiler could not read, about a model it had read.
 */
final class ReadingEvidence {

    /** Where each reading took a clause in. */
    private final Map<RuleRef, Set<FactSubject>> spokenFor = new LinkedHashMap<>();

    /** Where a part of a clause was taken in by nothing, which no other part makes up for. */
    private final Map<RuleRef, Set<FactSubject>> left = new LinkedHashMap<>();

    /** A reading took {@code rule} in at {@code position}. */
    void record(RuleRef rule, FactSubject position) {
        spokenFor.computeIfAbsent(rule, _ -> new LinkedHashSet<>()).add(position);
    }

    /**
     * Whether a part of {@code rule} about one of {@code positions} was taken in by nothing.
     *
     * <p>Outranks every other answer about the rule. A clause half of which nothing read is a clause
     * nothing read, however well the other half went — so an end placed by one conjunct does not
     * answer for the conjunct beside it.
     */
    boolean anyLeftStanding(RuleRef rule, Collection<FactSubject> positions) {
        Set<FactSubject> standing = left.get(rule);
        return standing != null && positions.stream().anyMatch(standing::contains);
    }

    /** A part of {@code rule} was taken in by nothing, of the positions it named. */
    void leftStanding(RuleRef rule, Set<FactSubject> positions) {
        left.computeIfAbsent(rule, _ -> new LinkedHashSet<>()).addAll(positions);
    }

    /**
     * Whether anything took {@code rule} in, of a position named by any of {@code positions}.
     *
     * <p>Every name the position answers to, since a number is called one thing by the interval
     * algebra and another by everything else, and a clause reaching it is filed under whichever the
     * reading recognised.
     */
    boolean tookIn(RuleRef rule, Collection<FactSubject> positions) {
        if (anyLeftStanding(rule, positions)) {
            return false;
        }
        Set<FactSubject> here = spokenFor.get(rule);
        return here != null && positions.stream().anyMatch(here::contains);
    }
}
