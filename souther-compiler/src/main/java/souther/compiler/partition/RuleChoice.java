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
     * The first of {@code rules}, tried in order, whose derivation concludes something with no part
     * left unread; or, where none does, the first that took the expression at all; or null where
     * none did. A rule answers null where it does not take the expression.
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
        Derivation first = null;
        for (Supplier<Derivation> rule : rules) {
            int start = met.size();
            Derivation tried = rule.get();
            if (tried != null && !stopsAnywhere(trying.of(tried))) {
                // What the first rule kept met stands between this one's and what came before.
                met.subList(before, start).clear();
                return tried;
            }
            if (tried != null && first == null) {
                first = tried;
            } else {
                met.subList(start, met.size()).clear();
            }
        }
        return first;
    }

    /** Whether some part of {@code stated} is one nothing read. */
    static boolean stopsAnywhere(Proposition stated) {
        return switch (stated) {
            case Proposition.Unread _ -> true;
            case Proposition.All all -> all.parts().stream().anyMatch(RuleChoice::stopsAnywhere);
            case Proposition.Any any -> any.parts().stream().anyMatch(RuleChoice::stopsAnywhere);
            case Proposition.OnAnApplication applications -> applications.each().stream()
                    .anyMatch(RuleChoice::stopsAnywhere);
            case Proposition.Some some -> stopsAnywhere(some.ofTheElement());
            default -> false;
        };
    }
}
