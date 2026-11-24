package souther.compiler.partition;

import souther.compiler.meaning.Conclusion;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.Proposition;

import java.util.List;
import java.util.function.Supplier;

/**
 * Which of the rules that take one expression is the one it is read by.
 *
 * <p>Every rule tried at an expression is sound for the observation it is tried on, so two that read
 * all of the expression state the same thing of it and the first is as good as any. One that stopped
 * part of the way states less than one that did not, and is kept only where nothing did better.
 * Whether a rule read all of it is asked of what it concludes and not of the steps it took: a part
 * nothing read beside one that settles the whole — false, and something unread — leaves nothing
 * unread in what is stated.
 *
 * <p>What a rule met while it was being tried belongs to that rule. The parts of one not kept are
 * no parts of what is stated, so they are taken back out of what was met; and the parts nothing read
 * are numbered when the derivation kept is concluded, so a rule tried and set aside moves no number.
 */
final class RuleChoice {

    private RuleChoice() {}

    /**
     * The first of {@code rules}, tried in order, whose derivation states the most of the
     * expression ({@link HowMuchItStates}); or null where none took it. A rule answers null where
     * it does not take the expression, and none is tried past one that reads all of it over the
     * input.
     *
     * <p>What a candidate states is asked of {@code trying}, one concluding for every choice of one
     * reading. A candidate holds the steps of the parts under it, which were concluded when the
     * choice for each part was made; concluded again here, every expression would be concluded once
     * for each expression it stands under.
     *
     * @param met    what each rule adds to as it meets a part, left holding what the rule chosen
     *               met and nothing a rule set aside met
     * @param trying a concluding that concludes each step once ({@link Conclusion#reusing})
     */
    static <M> Derivation firstThatReadsIt(List<Supplier<Derivation>> rules, List<M> met,
                                           Conclusion trying) {
        int before = met.size();
        Derivation kept = null;
        HowMuchItStates keptStates = null;
        for (Supplier<Derivation> rule : rules) {
            int start = met.size();
            Derivation tried = rule.get();
            if (tried == null) {
                met.subList(start, met.size()).clear();
                continue;
            }
            HowMuchItStates states = HowMuchItStates.of(trying.of(tried));
            if (kept == null || states.compareTo(keptStates) < 0) {
                // What the rule kept so far met stands between this one's and what came before.
                met.subList(before, start).clear();
                kept = tried;
                keptStates = states;
            } else {
                met.subList(start, met.size()).clear();
            }
            if (keptStates == HowMuchItStates.ALL_OF_IT_OVER_THE_INPUT) {
                return kept;
            }
        }
        return kept;
    }

    /**
     * How much a rule's conclusion states of the expression, most first. Two rules that state as
     * much are as good as each other, and the first tried is kept.
     */
    private enum HowMuchItStates {

        /** Every part read, and each over the input: where the input has to stand is said. */
        ALL_OF_IT_OVER_THE_INPUT,

        /** Every part read, some of it over a number only a run works out
         *  ({@link Proposition#isOverWhatARunWorksOut}): the runs place it, and where the input
         *  has to stand for it is not said. */
        ALL_OF_IT_ON_THE_RUNS,

        /** Some part unread, and which is said: it is made of parts, as a statement taken apart
         *  by its cases with every case unread still says which cases there are. */
        WHERE_IT_IS_UNREAD,

        /** One part nothing read. */
        NOTHING;

        static HowMuchItStates of(Proposition stated) {
            if (stopsAnywhere(stated)) {
                return stated instanceof Proposition.Unread ? NOTHING : WHERE_IT_IS_UNREAD;
            }
            return Proposition.isOverWhatARunWorksOut(stated) ? ALL_OF_IT_ON_THE_RUNS
                    : ALL_OF_IT_OVER_THE_INPUT;
        }
    }

    /** Whether some part of {@code stated} is one nothing read. */
    static boolean stopsAnywhere(Proposition stated) {
        return Proposition.leavesSomethingUnread(stated);
    }
}
