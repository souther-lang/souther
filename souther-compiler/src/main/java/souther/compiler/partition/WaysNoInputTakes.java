package souther.compiler.partition;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

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
