package souther.compiler.query;

import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.CompositionCapacity;
import souther.compiler.partition.CompositionRepertoire;
import souther.compiler.partition.Generator;
import souther.compiler.publish.CanonicalSelection;
import souther.compiler.publish.PublicationOrders;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.SequencedMap;
import java.util.function.Function;

/**
 * What composing a row for one rule of a decision came to.
 *
 * <p>One of the two axes a {@link RuleSettlement} holds, and the one about this compiler. Whether a
 * row is owed at the rule is {@link RuleRequirement}, and the two are answered by one search only
 * because composing is the instrument the first is asked through.
 *
 * <p><b>Three things happen and they were told apart by the absence of a word.</b> A settlement
 * carried the composing's shortfall where there was one and nothing where there was not, so nothing
 * stood for a candidate having been composed and for nobody having composed anything — the readings
 * settle some rules before a search is made, and those came out wearing the word for a search that
 * produced a row. A composing that came to nothing and proved the rule leaves no value is a third,
 * and read through that absence it could only be spelled as one of the two.
 *
 * <p>So what the search did is said here, and what the model says is said beside it. Neither is
 * recovered from the other.
 */
public sealed interface RuleSearch {

    /**
     * Nobody composed anything, because the readings settled the rule before a search was made.
     *
     * <p>A way that asks a position to be two things at once, and a way through an arm nothing
     * arrives at, are both answered off what is already read. Nothing was spent on them and there
     * is no word from a composing to say.
     */
    record NotMade() implements RuleSearch {}

    /**
     * A candidate was composed and tried, and what became of it is the requirement's to say.
     *
     * <p>Holds no row. What was built is carried by the requirement that was settled from it
     * ({@link RuleRequirement.Required#stoodBy()}), and a copy here would be a second answer about
     * one composing.
     */
    record Composed() implements RuleSearch {}

    /**
     * Nothing was composed, and what the composings came back with.
     *
     * <p>One per way of standing the dependencies in, because a rule is composed for once per way
     * and the ways may come back with different words. Whether those words say anything about the
     * model is the requirement's question and is answered over all of them at once
     * ({@link Adequacy.DecisionSearch#provedByEveryWay}); what is kept here is what each of them
     * said.
     *
     * <p>Each word with what the searches that came back with it met of this compiler's, joined by
     * the law the points of a border and the classes of an axis are joined by
     * ({@link souther.compiler.partition.CameToNothing#joined}). A word alone says
     * the rule is one nothing could compose a row for; what was met says whether a figure an
     * author could raise is what stopped it, and which.
     *
     * <p><b>In one order, whatever order the ways were walked in.</b> Two runs of one model that
     * met the ways in different orders hold one value, so nothing a reader is shown can come out of
     * the order a walk happened to take. Built through {@link #of} for that reason.
     */
    record CameToNothing(List<Came> ways) implements RuleSearch {

        public CameToNothing {
            ways = List.copyOf(ways);
            if (ways.isEmpty()) {
                throw new IllegalArgumentException(
                        "a composing that came to nothing says what it came to nothing on");
            }
        }

        /**
         * What the ways came back with, each word once and in the order a report says them.
         *
         * <p>Joined first, so that two ways with one word and two different figures are one word
         * having met both. Then by the place the word has among the reasons, which is the order
         * every other reader of these says them in, and by the whole of what each word says after —
         * two ways with one word and different conditions are two things said, and an order that
         * stopped at the word would leave which of them a reader sees to the walk. What was met is
         * no part of the order: it was added up under the word, so it is the same whichever way
         * met it first.
         */
        public static CameToNothing of(Collection<souther.compiler.partition.CameToNothing> ways) {
            return new CameToNothing(souther.compiler.partition.CameToNothing.joined(ways).stream()
                    .sorted(Comparator
                            .comparingInt((souther.compiler.partition.CameToNothing each) ->
                                    PublicationOrders.positionOf(each.why().reason()))
                            .thenComparing(each -> String.valueOf(each.why())))
                    .map(Came::of)
                    .toList());
        }
    }

    /**
     * One word the ways came back with, and what the searches that came back with it met of this
     * compiler's, each kind in the order a report says it in.
     *
     * <p>In that order here rather than as the sets a search adds them up in. A report says these,
     * and a set reaching it would be said in whatever order it iterates in. So the joining is done
     * on the sets ({@link souther.compiler.partition.CameToNothing#joined}) and what is kept is
     * the result put in order once.
     *
     * @param why         what the searches came to, in the words a report prints
     * @param figures     the figures that stopped them
     * @param populations what this compiler writes some of that they walked in part
     * @param unheld      the numbers they could not hold
     * @param planCut     the figures that cut short the plan they ran over, or left them none
     */
    record Came(Generator.UnresolvedCombination why,
                CanonicalSelection<CompositionBudget> figures,
                CanonicalSelection<CompositionRepertoire> populations,
                CanonicalSelection<CompositionCapacity> unheld,
                CanonicalSelection<CompositionBudget> planCut) {

        public Came {
            if (why == null || figures == null || populations == null || unheld == null
                    || planCut == null) {
                throw new IllegalArgumentException("a word the ways came back with says what they"
                        + " met, or that it was nothing");
            }
        }

        static Came of(souther.compiler.partition.CameToNothing came) {
            return new Came(came.why(),
                    PublicationOrders.COMPOSITION_BUDGETS.keep(came.met().figures()),
                    PublicationOrders.COMPOSITION_REPERTOIRES.keep(came.met().populations()),
                    PublicationOrders.COMPOSITION_CAPACITIES.keep(came.met().unheld()),
                    PublicationOrders.COMPOSITION_BUDGETS.keep(came.planCut()));
        }

        /**
         * These as a reader that shows less of a word than the word holds reads them: one for
         * each thing it shows, holding what every word shown alike met.
         *
         * <p>The law {@link souther.compiler.partition.CameToNothing#joinedAsShown} states, over
         * these. Two words that differ only in what a reader does not show are one sentence to it,
         * and written as two they are that sentence twice with half of what was met apiece.
         *
         * @param shown what the reader's sentence for a word is made from — the parts it prints,
         *              and not the sentence
         */
        public static List<Came> joinedAsShown(List<Came> all,
                                               Function<Generator.UnresolvedCombination, ?> shown) {
            SequencedMap<Object, Came> under = new LinkedHashMap<>();
            for (Came each : all) {
                under.merge(shown.apply(each.why()), each, Came::and);
            }
            return List.copyOf(under.values());
        }

        /** This and a word shown alike, as one holding what both met; the word kept is this one. */
        private Came and(Came other) {
            return new Came(why,
                    PublicationOrders.COMPOSITION_BUDGETS.keep(
                            both(figures.written(), other.figures().written())),
                    PublicationOrders.COMPOSITION_REPERTOIRES.keep(
                            both(populations.written(), other.populations().written())),
                    PublicationOrders.COMPOSITION_CAPACITIES.keep(
                            both(unheld.written(), other.unheld().written())),
                    PublicationOrders.COMPOSITION_BUDGETS.keep(
                            both(planCut.written(), other.planCut().written())));
        }

        private static <T> List<T> both(List<T> one, List<T> other) {
            List<T> out = new ArrayList<>(one);
            out.addAll(other);
            return out;
        }
    }
}
