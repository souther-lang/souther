package souther.compiler.partition;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;

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
     */
    private final Map<DecisionRule, Optional<NoInputTakesIt>> asked = new HashMap<>();

    /** Why no input takes {@code path}, where that is proved, asked once for what it consulted. */
    Optional<NoInputTakesIt> whyNoInputTakes(DecisionPath path,
                                             Function<DecisionPath, Optional<NoInputTakesIt>> proving) {
        return asked.computeIfAbsent(path.rule(), _ -> proving.apply(path));
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
