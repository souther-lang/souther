package souther.compiler.query;

import souther.compiler.partition.Generator;
import souther.compiler.publish.PublicationOrders;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.List;

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
     * Nothing was composed, and these are the words the composings came back with.
     *
     * <p>One per way of standing the dependencies in, because a rule is composed for once per way
     * and the ways may come back with different words. Whether those words say anything about the
     * model is the requirement's question and is answered over all of them at once
     * ({@link Adequacy.DecisionSearch#provedByEveryWay}); what is kept here is what each of them
     * said.
     *
     * <p><b>In one order, whatever order the ways were walked in.</b> Two runs of one model that
     * met the ways in different orders hold one value, so nothing a reader is shown can come out of
     * the order a walk happened to take. Built through {@link #of} for that reason, and a caller
     * that has one word says so with {@link #by}.
     */
    record CameToNothing(List<Generator.UnresolvedCombination> ways) implements RuleSearch {

        public CameToNothing {
            ways = List.copyOf(ways);
            if (ways.isEmpty()) {
                throw new IllegalArgumentException(
                        "a composing that came to nothing says what it came to nothing on");
            }
        }

        /**
         * The words the ways came back with, each once and in the order a report says them.
         *
         * <p>By the place the word has among the reasons first, which is the order every other
         * reader of these says them in, and by the whole of what each says after — two ways with
         * one word and different conditions are two things said, and an order that stopped at the
         * word would leave which of them a reader sees to the walk.
         */
        public static CameToNothing of(Collection<Generator.UnresolvedCombination> ways) {
            List<Generator.UnresolvedCombination> out = new ArrayList<>();
            for (Generator.UnresolvedCombination each : ways) {
                if (!out.contains(each)) {
                    out.add(each);
                }
            }
            out.sort(Comparator
                    .comparingInt((Generator.UnresolvedCombination each) ->
                            PublicationOrders.positionOf(each.reason()))
                    .thenComparing(String::valueOf));
            return new CameToNothing(out);
        }

        /** One word, for a caller whose composing was made once. */
        public static CameToNothing by(Generator.UnresolvedCombination why) {
            return of(List.of(why));
        }

        /**
         * The one word there is, for a caller that already knows the composing was made once.
         *
         * <p>Checked rather than assumed: a caller asking this of a rule whose ways came back with
         * two words is a caller reading one of them as the whole answer.
         */
        public Generator.UnresolvedCombination only() {
            if (ways.size() != 1) {
                throw new IllegalStateException(
                        "one word was asked for where the ways came back with " + ways.size()
                                + ": " + ways);
            }
            return ways.get(0);
        }
    }
}
