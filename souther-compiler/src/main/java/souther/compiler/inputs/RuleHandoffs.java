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
 * a shape this compiler cannot enter, or a recipient the descent named and nothing opened.
 *
 * <p>A depth this walk stops at is not one of them, though it reads like one. A stop at the depth
 * leaves the rules under it unread and hands nothing on
 * ({@code PathEngine.leftBy}), so no handing over is made there and none is left standing — which is
 * why a record four levels down is reported as a position nothing was read into and not also as one
 * whose rules nobody took (issue #1084).
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

    /**
     * That the reading rooted at {@code by} ended at {@code at} with rules under it still to be
     * read. Said by the reading, which is the only thing that knows it stopped.
     *
     * <p>Refuses a second reading owing one at the same position. Which reading answers for a
     * position is settled by where the descent last crossed an ownership boundary, so it is a
     * function of the path and there is one of them — and {@link #unresolvedAt} leans on that,
     * asking by position alone because a position has one owner to ask about.
     *
     * <p>Written down as a refusal because the projection is the whole risk. Every other step here
     * carries the pair, and one place that drops the origin is one place where a handoff owed by a
     * reading nobody kept could leave somebody else's position short — which is this issue's own
     * shape, an answer taken from something other than what established it. A traversal that puts
     * two readings under one path is this compiler contradicting itself and stops here, rather than
     * arriving as a position quietly reported short.
     */
    void owes(TermPath by, TermPath at) {
        for (Handoff each : owed) {
            if (each.at().equals(at) && !each.by().equals(by)) {
                throw new IllegalStateException(
                        "two readings answer for the rules at " + at + ": " + each.by()
                                + " and " + by);
            }
        }
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
     * <p>Nothing happens where no handoff was made at {@code at}. A descent opens readings whether
     * or not any rule is written under the position it came from, and a position nothing was owed at
     * has nothing to discharge.
     *
     * <p>Refused where a handoff was made and {@code child} is not one of the positions it passed
     * the rules to. That is the descent that enumerated the children and the descent that opened
     * them disagreeing, which is one walk contradicting itself rather than a state of the model —
     * and counting it anyway is what would let a reading nobody handed anything to discharge an
     * obligation.
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
     * How the reading that ended at {@code at} was left with rules under it that nothing took over,
     * or null where nothing is standing.
     *
     * <p>Every position the rules were passed to has to have been opened, and not merely some of
     * them: a sum whose second case nothing walked has left the rules of that case unread however
     * well the first went.
     *
     * <p>Asked by position and not by the pair the handoffs are held under, which is safe because
     * {@link #owes} refuses a second reading at one position. Left to be true rather than made so, a
     * handoff owed by one reading would answer for a position another reading reports — and an
     * answer taken from something other than what established it is what this issue was.
     *
     * <p>The first standing handoff answers. Two of them at one position would be two readings
     * answering for it, which {@link #owes} has already refused.
     */
    Shortfall unresolvedAt(TermPath at) {
        for (Handoff handoff : owed) {
            if (!handoff.at().equals(at)) {
                continue;
            }
            Set<TermPath> supposed = expected.get(handoff);
            if (supposed == null) {
                return new Shortfall.NothingExpected();
            }
            if (!accepted.getOrDefault(handoff, Set.of()).containsAll(supposed)) {
                return new Shortfall.NotFullyAccepted();
            }
        }
        return null;
    }

    /**
     * How a handing over was left standing, in this ledger's own words.
     *
     * <p><b>Why the descent got no further is not said here.</b> This knows that no recipient was
     * ever named, and that is a fact about the entries it holds; whether the walk was stopped by a
     * shape it cannot enter or went on and left a recipient unopened is a fact about the structural
     * reading, which this has never seen. Answered here, the ledger would be deciding what a
     * traversal means from the absence of an entry — the same reading of silence as evidence that
     * #1072 was about.
     *
     * <p>Whoever holds both readings joins them ({@code InputDomain}), and it is there that
     * {@link RulesLeftUnread.HandoffUnread} is settled.
     */
    sealed interface Shortfall {

        /** No recipient was ever named for the handing over: the descent past this position made no
         *  entry at all. */
        record NothingExpected() implements Shortfall {}

        /** Recipients were named and a reading was not opened at every one of them. */
        record NotFullyAccepted() implements Shortfall {}
    }
}
