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
     * What each way asked of comes to, by what it states: the ways a body is joined into, and the
     * ways a proof is had of as few conditions as still give it, ask about the same conditions
     * over and over.
     */
    private final Map<List<OnTheWay>, Optional<NoInputTakesIt>> asked = new HashMap<>();

    /** Why no input takes a way stating {@code stated}, where that is proved, asked once. */
    Optional<NoInputTakesIt> whyNoInputTakes(List<OnTheWay> stated,
                                             Function<List<OnTheWay>, Optional<NoInputTakesIt>> proving) {
        Optional<NoInputTakesIt> known = asked.get(stated);
        if (known == null) {
            known = proving.apply(stated);
            asked.put(List.copyOf(stated), known);
        }
        return known;
    }

    /** That no input takes {@code path}, for {@code why}. */
    void add(DecisionPath path, NoInputTakesIt why) {
        proved.putIfAbsent(path.rule(),
                new DecisionReading.ImpossiblePath(
                        new DecisionReading.Ruled(path.rule(), path.steps(), true), why));
    }

    /**
     * The ways proved, none of which another stands for. A way that consulted everything another
     * did and more is a way past that one, and its rules are the other's already: counted twice,
     * one set of rules no run takes would be two.
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
