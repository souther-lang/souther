package souther.compiler.partition;

import souther.compiler.publish.CanonicalSelection;
import souther.compiler.publish.PublicationOrders;

import java.util.Collection;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * A condition on the way to a border that a row for it was not composed against, and which stage
 * let it go.
 *
 * <p><b>Two stages, and a condition belongs to one of them at a time.</b> {@link OnTheWay} is the
 * walk's classification: a condition either landed in a vocabulary — the arithmetic's or the
 * positions' — or the walk had no words for it. A condition that landed and that the composer could
 * not then put a value under has not stopped being a cut, and saying so by writing it down a second
 * time as a decline would be one condition wearing two of the walk's answers.
 *
 * <p>So the walk's answer is kept and the stage is what this adds. What a reader of a point wants is
 * one list — everything the row it was offered, or not offered, was composed without — and which of
 * these each entry is says what would change it: a word this reading does not have, or a value this
 * composer cannot build.
 */
public sealed interface ReachabilityGap {

    /** Which question a report about the condition asks for its place, which is the condition's own
     *  answer and not a second one worked out here. */
    ConditionReportAnchor anchor();

    /** The walk had no words for it, so nothing downstream ever saw it. */
    record Unstated(OnTheWay.Declined condition) implements ReachabilityGap {

        @Override
        public ConditionReportAnchor anchor() {
            return condition.anchor();
        }
    }

    /**
     * The walk stated it and nothing composed a value under it.
     *
     * <p>Carrying the cut and not a copy of what it said. The condition is the same one the walk
     * took in — a report may say which positions it is over, and a reader asking why the row does
     * not meet it is asking about that cut — so what is added here is the stage and the reason, and
     * the condition keeps the identity it was given.
     */
    record Uncomposed(OnTheWay.TakenIn condition, Why why) implements ReachabilityGap {

        @Override
        public ConditionReportAnchor anchor() {
            return condition.anchor();
        }
    }

    /**
     * The walk stated it, and the rules of the way it is on leave nothing.
     *
     * <p>Apart from {@link Uncomposed} and not one of its reasons, because it is not one. Every
     * {@link Why} says what this composer did not manage, and a reader may act on none of them; this
     * says what the model settles, and a reader may act on it (ADR-0091). Held as a fourth reason,
     * the two kinds of news would be one list that a reader has to sort by hand — and the sentence
     * saying a figure could be raised would be written for a condition no figure reaches.
     *
     * <p>No figure travels with it. Nothing was walked: the proof was there before any value was
     * chosen, which is what makes it worth saying rather than what a search came to.
     *
     * <p><b>The condition is where the proof was met and not what the proof is about.</b> What was
     * shown empty is the region the way narrowed — every condition on it taken together, and
     * whatever the row has fixed — so this one is the place a reader is sent and not the one that
     * closed it. Attributing the proof to the way itself is {@link Reachability}'s to do and is not
     * done here; until it is, what a report says of this has to stay what is known, which is that
     * the way's conditions leave nothing standing together.
     */
    record ProvedImpossible(OnTheWay.TakenIn condition) implements ReachabilityGap {

        @Override
        public ConditionReportAnchor anchor() {
            return condition.anchor();
        }
    }

    /**
     * What a cut comes to where it could be written several ways and none of them was placed.
     *
     * <p><b>The rules leave nothing only where every way was shown to leave nothing</b>, and no
     * way was left unlooked at. The rules leaving one case of a sum nothing say nothing about the
     * case beside it, and a way this compiler did not get to the end of may have the values the
     * others lacked — so anything short of every way proved is this compiler not composing the cut,
     * which a reader may conclude nothing about the model from.
     *
     * <p>Said in the words of what stopped it, and the same words whichever order the ways were
     * walked in. The order is the order the model declares its cases in, and a report that changed
     * with it would be telling a reader about the declaration rather than the cut.
     *
     * <p>A figure that stopped one of the ways is said before anything else, because raising it is
     * something a reader can do and may find the row. Two numbers met at one location is said
     * before a way that found nothing, since it names the population this compiler does not compose
     * rather than only that nothing was found.
     *
     * @param ways          what each way that was looked at came to
     * @param someUnsettled whether some way was not looked at to its end — one whose place nothing
     *                      worked out, or one the row could not be beside what it already was
     */
    static ReachabilityGap overEveryWay(OnTheWay.TakenIn cut, List<ReachabilityGap> ways,
                                        boolean someUnsettled) {
        if (!someUnsettled && !ways.isEmpty()
                && ways.stream().allMatch(each -> each instanceof ProvedImpossible)) {
            return new ProvedImpossible(cut);
        }
        Set<CompositionBudget> stoppedBy = EnumSet.noneOf(CompositionBudget.class);
        Set<CompositionCapacity> unheld = new HashSet<>();
        boolean twoAtOneLocation = false;
        for (ReachabilityGap each : ways) {
            switch (each) {
                case Uncomposed(var _, Why.TheWalkForItsPositionsWasStopped(var by, var notHeld)) -> {
                    stoppedBy.addAll(by.written());
                    unheld.addAll(notHeld.written());
                }
                case Uncomposed(var _, Why.TwoNumbersAtOneLocation _) -> twoAtOneLocation = true;
                case Uncomposed(var _, Why.NoValueComposedForItsPositions _),
                     ProvedImpossible _ -> { }
                case Unstated _ -> throw new IllegalArgumentException(
                        "a way of writing a cut is one the walk stated: " + each);
            }
        }
        if (!stoppedBy.isEmpty() || !unheld.isEmpty()) {
            return new Uncomposed(cut, Why.TheWalkForItsPositionsWasStopped.by(stoppedBy, unheld));
        }
        return new Uncomposed(cut, twoAtOneLocation
                ? new Why.TwoNumbersAtOneLocation()
                : new Why.NoValueComposedForItsPositions());
    }

    /**
     * What stopped a stated condition from being composed against.
     *
     * <p>Each says what this composer did rather than what the model says. A row is written without
     * the condition either way, so nothing read off one of these says the condition cannot be met —
     * and a word going away is a capability gained.
     */
    sealed interface Why {

        /**
         * No value was composed at some position the condition is over.
         *
         * <p>Said of the whole condition, because a cut over two positions is one statement about
         * the pair. One of them put where the cut admits and the other left to its own declared
         * range is not half the condition holding — it is the condition not holding, with a
         * position pinned on the strength of it. So a condition this cannot place every position of
         * is placed at none of them.
         */
        record NoValueComposedForItsPositions() implements Why {}

        /**
         * The same, where a budget of this compiler's, or a value it could not hold, is what stopped
         * the walk that would have placed the positions.
         *
         * <p>A case beside the one above rather than a field on it. The two are different news: one
         * says nothing was found in what was walked, the other says the walking stopped, and only
         * the second names something a reader could raise. Held as a set that is sometimes empty,
         * every reader would decide again which of the two it had.
         *
         * <p>Not an {@link souther.compiler.query.EstablishmentGap}. A row was composed here; what
         * the budget cost is one condition on the way being composed against, and reporting it as a
         * point nothing could be established at would say more than happened.
         */
        record TheWalkForItsPositionsWasStopped(CanonicalSelection<CompositionBudget> by,
                                                CanonicalSelection<CompositionCapacity> unheld)
                implements Why {

            /**
             * Stopped by a figure, by a value it could not hold, or by both: the walk that would
             * have placed the positions did not reach its end either way, and each is said in its
             * own vocabulary since what a reader does about them differs.
             */
            public TheWalkForItsPositionsWasStopped {
                if (by == null || unheld == null || (by.isEmpty() && unheld.isEmpty())) {
                    throw new IllegalArgumentException("a walk this compiler stopped says what"
                            + " stopped it: a budget, or a value it could not hold");
                }
            }

            /** What a walk met, in the order a report says it. */
            public static TheWalkForItsPositionsWasStopped by(Collection<CompositionBudget> met,
                                                              Collection<CompositionCapacity> unheld) {
                return new TheWalkForItsPositionsWasStopped(
                        PublicationOrders.COMPOSITION_BUDGETS.keep(met),
                        PublicationOrders.COMPOSITION_CAPACITIES.keep(unheld));
            }
        }

        /**
         * Two numbers taken at one location, one of which the row is already being written for.
         *
         * <p>A row writes one value where a location is, and that one value would have to answer
         * both — two of the totals inside one container. Which other number it meets is not part
         * of it: the row may be writing that location for the item it is composed at, or for a
         * condition on the way that was taken in before this one. Told apart from the one above
         * because only this one is about two demands meeting at a location rather than about what
         * could be built at a position.
         *
         * <p>Which pairs those are is the realizer's answer and not a list here. A pair it composes
         * one value for reaches this reader as a location placed and not as a gap, and the pairs it
         * composes one for are every pair the models of this repository write.
         *
         * <p><b>Which is why this stays.</b> What the realizer answers of a group it has no way for
         * is a population it writes some of, and this is the word for that answer on the way to a
         * point. Taken out, a group of a kind nobody has written the composing for would fall to
         * the reader beside it — a condition on positions nothing composed a value at — and the
         * author of a model whose numbers this compiler cannot put together would be told that its
         * positions hold no value.
         */
        record TwoNumbersAtOneLocation() implements Why {}
    }
}
