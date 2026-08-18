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
 * <p>Success and not attempt. A reading that recognised part of a clause and gave up took nothing
 * in, so nothing here records it — what is written down is the point at which a reading adopted the
 * clause into what it holds.
 *
 * <p><b>Every reading, and each one asked at its own adoption point.</b> There are more of them than
 * a reader notices: {@code value * 2 >= 4} is beyond the reading of ends and beyond the reading of
 * values, and the reading that builds the numeric constraints takes it in whole. An accounting that
 * consulted two of the three would report that clause exactly the way #842 reports a bound — as a
 * rule this compiler could not read, about a model it had read.
 */
final class ReadingEvidence {

    /** Where each reading took a clause in. */
    private final Map<Clause.Ref, Set<FactSubject>> spokenFor = new LinkedHashMap<>();

    /** A reading took {@code rule} in at {@code position}. */
    void record(Clause.Ref rule, FactSubject position) {
        spokenFor.computeIfAbsent(rule, _ -> new LinkedHashSet<>()).add(position);
    }

    /**
     * Whether anything took {@code rule} in, of a position named by any of {@code positions}.
     *
     * <p>Every name the position answers to, since a number is called one thing by the interval
     * algebra and another by everything else, and a clause reaching it is filed under whichever the
     * reading recognised.
     */
    boolean tookIn(Clause.Ref rule, Collection<FactSubject> positions) {
        Set<FactSubject> here = spokenFor.get(rule);
        return here != null && positions.stream().anyMatch(here::contains);
    }
}
