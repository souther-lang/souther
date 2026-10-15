package souther.compiler.partition;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Supplier;

/**
 * The ways one reading of a body proved no input takes, as it proves them
 * ({@link DecisionNaming#join}).
 *
 * <p>One register for the body, shared down every scope as the names of its conditions are: a way
 * proved closed under a binding is the same way outside it.
 */
final class WaysNoInputTakes {

    /** Each way once, by what it consulted, with the first proof had of it. */
    private final Map<DecisionRule, DecisionReading.ImpossiblePath> proved = new LinkedHashMap<>();

    /**
     * What each way asked of comes to, by what it consulted: the ways a body is joined into, and
     * the ways a proof is had of as few conditions as still give it, ask about the same conditions
     * over and over, met in one order or another. What a way states is what each condition it
     * consulted states coming out as it did, which the reading of the body answers once.
     *
     * <p>Keyed by the rule, while the proof reads what each condition states. The two are one
     * question because a condition states one thing however often a way consults it
     * ({@link DecisionPath.Consulted#again}): two ways that are the same rule state the same of the
     * input. A condition whose statement turned on where it was consulted would have to be a
     * condition of its own, or this would answer one way with another's proof.
     */
    private final Map<DecisionRule, Optional<NoInputTakesIt>> asked = new HashMap<>();

    /** How many more conditions this reading takes in, in all
     *  ({@link CompositionBudget#CONDITIONS_A_DECISION_TAKES_IN_TO_PROVE}). */
    private int takenInLeft = CompositionBudget.CONDITIONS_A_DECISION_TAKES_IN_TO_PROVE.maximum();

    /**
     * Why no input takes {@code path}, where that is proved, asked once for what it consulted —
     * and nothing once this reading has taken in as many conditions as it does in all, which is no
     * proof and keeps the way.
     */
    Optional<NoInputTakesIt> whyNoInputTakes(DecisionRule consulted,
                                             Supplier<Optional<NoInputTakesIt>> proving) {
        Optional<NoInputTakesIt> known = asked.get(consulted);
        if (known != null) {
            return known;
        }
        if (takenInLeft == 0) {
            return Optional.empty();
        }
        Optional<NoInputTakesIt> answered = proving.get();
        asked.put(consulted, answered);
        return answered;
    }

    /**
     * Whether a proof may take one more condition in, counting it if so. A walk told no takes the
     * condition in as nothing, which narrows nothing and so proves nothing past it.
     */
    boolean takesIn() {
        if (takenInLeft == 0) {
            return false;
        }
        takenInLeft--;
        return true;
    }

    /** That no input takes {@code path}, for {@code why}. */
    void add(DecisionPath path, NoInputTakesIt why) {
        proved.putIfAbsent(path.rule(),
                new DecisionReading.ImpossiblePath(
                        new DecisionReading.Ruled(path.rule(), path.steps(), true), why));
    }

    /**
     * The ways proved, none of which another stands for. A way that consulted everything another
     * did and more is a way past that one, and its rules are the other's already. Two ways neither
     * of which stands for the other may still both stand for some rule — two proofs had of
     * different conditions — and each is a proof of its own, so both are said.
     */
    List<DecisionReading.ImpossiblePath> leastOfThem() {
        List<DecisionReading.ImpossiblePath> out = new ArrayList<>();
        for (DecisionReading.ImpossiblePath each : proved.values()) {
            boolean pastAnother = proved.values().stream().anyMatch(other -> other != each
                    && other.standsFor(each.way().rule()));
            if (!pastAnother) {
                out.add(each);
            }
        }
        return List.copyOf(out);
    }
}
