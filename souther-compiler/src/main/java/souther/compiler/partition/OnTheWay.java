package souther.compiler.partition;

import souther.compiler.inputs.NameReach;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.WhyNotTaken;

import java.util.LinkedHashSet;
import java.util.List;

/**
 * One condition on the way to a comparison, and what became of it.
 *
 * <p>Both halves, because a region says nothing about how it was arrived at. What the walk took in
 * is what a composer builds a row to meet, and a region carries the part of that it can say; what
 * the walk could not take in is why the search may be looking over rows that never arrive. Kept as
 * one sequence in the order the walk met them, so that a reader asking either question asks the
 * same list — split into two at the seam, "nothing stood on the way" and "everything on the way was
 * taken in" come out as the same empty answer, which is the reading a report cannot make and the
 * one an author needs.
 *
 * <p><b>Every condition is one of these, and which is not a choice about the shape it was written
 * in.</b> A condition either lands in a vocabulary a search can compose against — the arithmetic's
 * ({@link TakenIn}) or the positions' ({@link Narrowed}) — or its answer is the same for every row
 * ({@link Settled}), or it is {@link Declined}. What a search composes against is one list either
 * way: what a condition taken in asks of a row is {@link RowDemand}'s answer and not another arm
 * here. So a fork this reading learns to walk later widens what a search can reach and can never
 * quietly leave a condition off: a reader that cannot state one says so here, and a row composed
 * under a declined condition is a row that may not arrive rather than a row nothing knew about.
 *
 * <p>And a condition the source settles is not one this reading could not state. That it asks
 * nothing of a row, or that no row comes out of it this way, is what it says — and read as declined,
 * a way past one would be reported as a way this compiler fell short on, and a way no row takes as
 * one a row was owed for.
 *
 * <p>Collected where the condition is met and never worked out afterwards from where a comparison
 * sits, which is the rule {@link souther.compiler.reach.PathDecision} is written to as well.
 */
public sealed interface OnTheWay {

    /**
     * Which question a report about it asks for its place.
     *
     * <p>An anchor and not a place. A location held here reaches whoever reads a finding, so a
     * helper whose conditions move — saying the same thing — would move every answer about them;
     * what is held is which question to put, and the place is worked out where a sentence is
     * written.
     */
    ConditionReportAnchor anchor();

    /**
     * A condition a search can compose a row against, and what it came to.
     *
     * <p>The demand is what says which condition this is. Two of them asking one thing of a row are
     * one thing to compose against, and nothing here needs to tell them apart.
     *
     * <p>What it asks is {@link RowDemand}'s answer and not a second arm here. A rule over numbers,
     * a rule over a carrier's own values and whatever a composer learns to build next are all
     * conditions a row has to pass, and a reader asking what the way took in asks one list.
     */
    record TakenIn(ConditionReportAnchor anchor, RowDemand.OfACondition demand)
            implements OnTheWay {}

    /**
     * A condition that says which values a position is one of, as the position it narrows.
     *
     * <p>What a fork on a sum states. Reaching the arm is the scrutinee having turned out to be the
     * case the arm selects, and that is a narrowing of the position the scrutinee is at — which is
     * a thing a row can be composed to be, while "this arm was taken" is not.
     *
     * <p>The narrowed position and not the pair it is made of. What has to hold of the parameter
     * for such a position to exist in it is {@link #requirements()}, read off the position, which
     * is where every other reader of a narrowing asks; carried as a position and a refinement side
     * by side, this would be the one place that splits them its own way.
     *
     * <p><b>Or a name the cases of a sum share, narrowed.</b> {@code r.q.flag} is readable on a
     * value of {@code Q} and stands under whichever case the value turns out to be, so a fork on it
     * narrows the value at the name, and that is a requirement under each case rather than at any
     * one position. The crossings are what says where the name stands once a case is chosen, and
     * they are what makes the requirement move there ({@link Requirements}); at an ordinary
     * position there are none.
     *
     * <p>The position is what says which condition this is, the way a cut does for the one above.
     *
     * <p><b>And what the same narrowing says on the position's own order, where it has one.</b> The
     * cases of an enumeration are places on the order its declaration writes, so a value that
     * turned out to be {@code Low} or {@code Mid} is a value away from {@code High} — one fact said
     * in the second vocabulary, which a region can carry and a requirement cannot. Read off the
     * position when the entry is made and not here, because which order a position stands on is
     * the reading's answer.
     *
     * @param position   the scrutinee's position with the arm's case narrowed onto it
     * @param crossings  where the names {@code position} steps through stand once the sum above
     *                   each is one of its cases; only the ones some name of it crosses are kept
     * @param onItsOrder the places of its order the narrowing leaves out, one hole each; empty
     *                   where the position stands on no enumeration's order
     */
    record Narrowed(ConditionReportAnchor anchor, TermPath position,
                    List<NameReach.Crossing> crossings,
                    List<TakenConstraint.AwayFrom> onItsOrder) implements OnTheWay {

        public Narrowed {
            if (position == null || !position.narrowsWhatItReaches()) {
                throw new IllegalArgumentException(
                        "a narrowing on the way is a position read as one of its cases: " + position);
            }
            crossings = Requirements.of(position, crossings).crossings();
            onItsOrder = List.copyOf(onItsOrder);
        }

        /** What has to hold of the parameter for a row to be past this narrowing. */
        public Requirements requirements() {
            return Requirements.of(position, crossings);
        }
    }

    /**
     * A condition whose answer is the same for every row, and whether that answer is the way the
     * walk went.
     *
     * <p>Two facts about the model and neither a demand nor a decline. Coming out this way for
     * every row, it asks nothing of one — a composer has nothing to build against and nothing was
     * left unstated. Coming out the other way for every row, no row takes the way past it, which is
     * {@link Reachability.NothingComesOutThatWay}: a border down it is one nothing reaches, and a
     * search composing for it would be looking for a row that does not exist.
     *
     * <p>Named, for the reason {@link Declined} is: what this carries beside the anchor is one bit,
     * and two conditions settled the same way are not one condition.
     *
     * @param condition which condition of the reading is settled
     * @param thisWay   whether every row brings it out the way the walk went
     */
    record Settled(ConditionOccurrence condition, ConditionReportAnchor anchor, boolean thisWay)
            implements OnTheWay {

        public Settled {
            if (condition == null) {
                throw new IllegalArgumentException(
                        "a condition the source settles is some condition the reading met");
            }
            // Named and placed as {@link Declined} is, and held to the same: the anchor and the
            // name are one answer said twice.
            if (anchor instanceof ConditionReportAnchor.WhereTheReadingMetIt(
                    String _, ConditionOccurrence anchored) && !condition.equals(anchored)) {
                throw new IllegalArgumentException("a condition settled here is reported here: "
                        + condition + " reported at " + anchored);
            }
        }
    }

    /**
     * A condition nothing here could turn into a cut, and what stopped it.
     *
     * <p><b>One that has to say which condition it is.</b> What a demand or a narrowing carries
     * beside the anchor already tells one from its neighbours: a cut is an inequality over a form,
     * a narrowing is a position. What this carries beside the anchor is only why it was
     * declined, and two conditions declined for one reason are one reason — so without a name for
     * the condition, two conditions this compiler does tell apart would be one value.
     *
     * <p>Named and not placed. Where two of them are written is what used to tell them apart, which
     * is a location doing identity's work because nothing else was doing it.
     *
     * <p>Every reason, and not the first. A condition made of parts can be declined for one reason
     * in one part and another in the next — one part's meaning unread, the whole a shape this
     * reading has no demand for — and each is a different thing for somebody to do, so none stands
     * in for another.
     *
     * @param condition which condition of the reading was declined
     * @param whys      why, each once, in the order met
     */
    record Declined(ConditionOccurrence condition, ConditionReportAnchor anchor,
                    List<WhyNotTaken> whys)
            implements OnTheWay {

        public Declined(ConditionOccurrence condition, ConditionReportAnchor anchor,
                        WhyNotTaken why) {
            this(condition, anchor, List.of(why));
        }

        public Declined {
            if (condition == null) {
                throw new IllegalArgumentException(
                        "a condition this reading declined is some condition it met");
            }
            whys = List.copyOf(new LinkedHashSet<>(whys));
            if (whys.isEmpty()) {
                throw new IllegalArgumentException("a condition is declined for some reason");
            }
            // And the one it is named after is the one a report is sent to. Where the reading
            // places it, the anchor says which condition of the reading that is — so the two are
            // one answer said twice, and a value whose halves named different conditions would be
            // reported at a condition other than the one it says was declined.
            if (anchor instanceof ConditionReportAnchor.WhereTheReadingMetIt(
                    String _, ConditionOccurrence anchored) && !condition.equals(anchored)) {
                throw new IllegalArgumentException("a condition declined here is reported here: "
                        + condition + " reported at " + anchored);
            }
        }
    }
}
