package souther.compiler.partition;

import souther.compiler.inputs.NameReach;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.WhyUnread;

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
     * @param condition which condition of the reading was declined
     */
    record Declined(ConditionOccurrence condition, ConditionReportAnchor anchor, Why why)
            implements OnTheWay {

        public Declined {
            if (condition == null) {
                throw new IllegalArgumentException(
                        "a condition this reading declined is some condition it met");
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

    /**
     * What stopped a condition from being stated in either vocabulary.
     *
     * <p>The walk's own answers and no other stage's. A condition this stated and something later
     * could not act on is still stated — it keeps the answer given here and what became of it
     * downstream is {@link ReachabilityGap}'s. Written as another word here, one condition would
     * wear two of these.
     *
     * <p>Each says what this reading did rather than what the model says. A condition an author
     * wrote plainly is here wherever nothing here has a way of carrying it, so nothing read off one
     * of these says a row cannot be written, and a word going away is a capability gained rather
     * than a model changed.
     *
     * <p><b>Not the reason the same comparison gets for drawing no line.</b>
     * {@link UnreadComparison} answers why a comparison did not become a boundary, which is a
     * different question with different answers: {@code 1 < 2} comes back there as a form nothing
     * reads, when what happened is that it constrains no position; and a comparison this
     * arithmetic cannot carry comes back as one relating two positions, when a relation between two
     * positions is exactly what a cut over a {@code LinearForm} does carry. Borrowed here, either
     * would send an author after the wrong thing.
     *
     * <p>So what is said about a comparison is what is known about it here, and no more. The finer
     * answer belongs to whatever decided — {@link AffineReading}, which returns nothing and says
     * nothing about why — and it is not invented at this end from the shape of what it was given.
     */
    sealed interface Why extends WhyUnread {

        /** A condition that is neither a comparison nor a combination of them, so nothing was read
         *  of it. */
        record NoWordsForTheShape() implements Why {}

        /**
         * A comparison this reading did not turn into a cut.
         *
         * <p>One word, because one word is what this end knows. A comparison naming no position, a
         * form outside the arithmetic and a subject with no spacing for its values arrive here as
         * one absence, and {@link AffineReading} is where they would be told apart.
         */
        record ComparisonNotRepresentedAsACut() implements Why {}

        /**
         * A comparison read from end to end whose quantity stands on no order a region measures
         * values on.
         *
         * <p>Apart from the two above, and from both directions. It is not a reading that fell
         * short: {@code a == b} over two records is read perfectly, and what it comes to is a
         * difference between two positions that is a distance on nothing. And it is not a rule
         * that constrains no position: it constrains both of them, and an author reading that it
         * constrains none would go looking for a cancellation that is not there.
         *
         * <p>What is here for an author to act on is the carrier. A position whose values this
         * compiler measures on nothing is one every rule about it is unrepresented in, so the
         * shortfall is where the model's own type has no order rather than in how the rule was
         * written.
         */
        record QuantityStandsOnNoOrder() implements Why {}

        /**
         * What the condition coming out this way says is one of two things, and a region is what
         * has been accumulated onto it. {@code A && B} coming out false says one of them failed and
         * names neither, and taking either would exclude rows that arrive.
         */
        record OneOfTwoThings() implements Why {}

        /**
         * An arm of a fork this reading could not state as a narrowing of a position.
         *
         * <p>A fork on something no position holds — an expression the walk cannot follow back to
         * one, an arm answering for several cases at once, a case the reading of the declarations
         * has no position for, an attempt whose arm is decided by an invariant the walk does not
         * read. Each of those leaves the same thing unsaid, which is which values of the input
         * reach this arm, so they arrive here as one word.
         */
        record ForkArmNotReadAsANarrowing() implements Why {}

        /**
         * A condition about what a container holds, over a container this reading could not
         * follow to a position of the input.
         *
         * <p>What such a condition asks of a row is something of the container's elements, and an
         * element is somewhere only where the container is: with no position for the container
         * there is nowhere for what is asked of its elements to be written.
         */
        record ContainerAtNoPosition() implements Why {}

        /**
         * A condition about whether a container holds a value, where the value stands at no
         * position of the input.
         *
         * <p>Read and not of a shape this has no words for: the container is at a position and
         * what is asked of it is plain. What is missing is somewhere to read the value from — a
         * value written in the source, or one a helper builds — and what a row would hold is
         * that value, which nothing here writes into the container yet.
         */
        record ValueAtNoPosition() implements Why {}

        /**
         * A condition every element of a container has to meet, which says something of more than
         * the element.
         *
         * <p>Every element meeting it is also what an empty container does, whatever the rest of
         * the condition says. So where the condition is about something beside the element, a row
         * past it need not meet that part — and narrowing on it would exclude rows that arrive.
         */
        record MoreThanEachElement() implements Why {}

        /**
         * What a container's elements are asked for comes to how many it holds, and that is no
         * number this reading can state of it.
         *
         * <p>Some element meeting what every element meets is the container holding one, and every
         * element meeting what none meets is the container holding none. Where its size is no
         * number of the input a region measures, neither can be put to a row — and saying nothing
         * instead would be a condition read as asking nothing.
         */
        record SizeOfTheContainerNotStated() implements Why {}

    }
}
