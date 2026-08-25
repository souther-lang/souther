package souther.compiler.inputs;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * Where a reading of a value ended with the rules under a position still to be read, and what took
 * them over.
 *
 * <p>A reading of a declaration stops where no declaration stands to be read: at a container, at an
 * optional, at a choice between declarations. What is written under one of those is written about a
 * value one position down, so the rules are not lost there — the responsibility for them is somebody
 * else's. Which is a claim about the walk over positions, and nothing in the reading that stopped
 * can settle it.
 *
 * <p><b>Taking the rules over is an act, not a coincidence.</b> Every entry here is made by the
 * descent that made it true: the reading that stopped says it owes one ({@link #owes}), the descent
 * that crosses the boundary says which values are supposed to take the rules ({@link #passesTo}),
 * and each reading actually opened says it took them ({@link #accepts}). Nothing is worked out
 * afterwards by looking at which readings happen to exist under a path. Read that way, a reading
 * opened under the position for some other purpose would discharge an obligation it never heard of —
 * which is the same mistake as reading "no failure was recorded" as "everything was read", and it is
 * the mistake this issue was (#1072).
 *
 * <p><b>Handing the rules over is not the same as reading them.</b> A reading that was opened and
 * then came back short of something reports that shortfall itself, at its own position. The handoff
 * above it is discharged all the same: the rules reached a reader, and saying so twice would report
 * one gap at two positions. What leaves a handoff standing is that no reading was opened at all —
 * a shape this compiler cannot enter, a depth this walk stops at, a value it has already been to.
 */
final class RuleHandoffs {

    /**
     * One handing over: the reading that ended, and the position it ended at.
     *
     * <p>The reading and not the position alone. A path says where something is, which is not the
     * same as who was answering for the rules there — and an obligation identified by where it sits
     * is one any reading that reaches the same place can be taken to have met.
     *
     * @param by the value whose rules were being read, named by where that reading is rooted
     * @param at the position that reading stopped at
     */
    record Handoff(TermPath by, TermPath at) {}

    /** The handoffs made, in the order the walk made them. */
    private final Set<Handoff> owed = new LinkedHashSet<>();
    /** Which positions are supposed to take the rules over, for the handoffs a descent has reached.
     *  Absent for one nothing has reached, which is what leaves it standing. */
    private final Map<Handoff, Set<TermPath>> expected = new LinkedHashMap<>();
    /** And which of them a reading was actually opened at. */
    private final Map<Handoff, Set<TermPath>> accepted = new LinkedHashMap<>();

    /** That the reading rooted at {@code by} ended at {@code at} with rules under it still to be
     *  read. Said by the reading, which is the only thing that knows it stopped. */
    void owes(TermPath by, TermPath at) {
        owed.add(new Handoff(by, at));
    }

    /**
     * That the descent past {@code at} is supposed to open a reading at each of {@code children}.
     *
     * <p>Said where the children are enumerated and nowhere else. What a sum's cases are and which
     * of them the rules leave anything at is settled once, by the descent, and the set it settled is
     * what this handoff is measured against — worked out again from the readings that exist, a case
     * nothing walked would be a case nobody expected.
     *
     * <p>Does nothing where no handoff was made at {@code at}. A descent crosses a boundary whether
     * or not any rule is written under it, and a position nothing was owed at owes nothing.
     */
    void passesTo(TermPath by, TermPath at, Collection<TermPath> children) {
        Handoff handoff = new Handoff(by, at);
        if (owed.contains(handoff)) {
            expected.put(handoff, new LinkedHashSet<>(children));
        }
    }

    /**
     * That a reading was opened at {@code child}, which is one of the positions {@code at} passed
     * the rules to.
     *
     * <p>Refused for a position nothing said to expect. A reading opened somewhere nobody handed
     * anything to is a reading about something else, and counting it here is what would let an
     * unrelated root discharge an obligation.
     */
    void accepts(TermPath by, TermPath at, TermPath child) {
        Handoff handoff = new Handoff(by, at);
        if (!owed.contains(handoff)) {
            return;
        }
        Set<TermPath> supposed = expected.get(handoff);
        if (supposed == null || !supposed.contains(child)) {
            throw new IllegalArgumentException(
                    "a reading at " + child + " was not one the handoff at " + at
                            + " passed the rules to: " + supposed);
        }
        accepted.computeIfAbsent(handoff, _ -> new LinkedHashSet<>()).add(child);
    }

    /**
     * Whether some reading ended at {@code at} with rules under it that nothing took over.
     *
     * <p>Every position the rules were passed to has to have been opened, and not merely some of
     * them: a sum whose second case nothing walked has left the rules of that case unread however
     * well the first went.
     */
    boolean unresolvedAt(TermPath at) {
        for (Handoff handoff : owed) {
            if (handoff.at().equals(at) && !resolved(handoff)) {
                return true;
            }
        }
        return false;
    }

    private boolean resolved(Handoff handoff) {
        Set<TermPath> supposed = expected.get(handoff);
        return supposed != null
                && accepted.getOrDefault(handoff, Set.of()).containsAll(supposed);
    }
}
