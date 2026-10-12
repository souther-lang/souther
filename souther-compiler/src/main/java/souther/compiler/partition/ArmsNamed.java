package souther.compiler.partition;

import souther.compiler.types.ModelOccurrence;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The case each arm of a {@code match} is, as the tree the language's own operations stand in names
 * the value matched.
 *
 * <p>For the arms the reading of the runs could not name. That reading walks the tree where an
 * operation handing a closure the elements of a container is expanded, so a name the closure is
 * handed stands for no position there and an arm on it is a
 * {@link souther.compiler.reading.Condition.Arm} with no subject. Where the operation still stands,
 * the name is the element it was handed, and the arm is a case of that element.
 *
 * <p>Joined on the construct of the model the two readings agree about ({@link ModelOccurrence}),
 * which is what the readings of the comparisons are joined on as well. A construct the second
 * reading met at more than one position names none of them.
 *
 * @param byFork the cases of each fork's arms, in the order of its arms
 */
public record ArmsNamed(
        Map<ModelOccurrence, List<souther.compiler.reading.Condition.Case>> byFork) {

    public static final ArmsNamed NONE = new ArmsNamed(Map.of());

    public ArmsNamed {
        Map<ModelOccurrence, List<souther.compiler.reading.Condition.Case>> copied =
                new LinkedHashMap<>();
        byFork.forEach((fork, cases) -> copied.put(fork, List.copyOf(cases)));
        byFork = Map.copyOf(copied);
    }

    /** The case {@code arm} is, or empty where nothing named the value its fork matches. */
    public Optional<souther.compiler.reading.Condition.Case> of(
            souther.compiler.reading.Condition.Arm arm) {
        List<souther.compiler.reading.Condition.Case> cases =
                ModelOccurrence.statedAt(arm.arm().fork()).map(byFork::get).orElse(null);
        if (cases == null) {
            return Optional.empty();
        }
        // One construct of the model, read in two trees, with the arms it was written with in
        // both. An arm one of them has and the other lacks is the two disagreeing about the body.
        if (arm.arm().part() >= cases.size()) {
            throw new IllegalStateException("arm " + arm.arm() + " of a fork named with "
                    + cases.size() + " arms");
        }
        return Optional.of(cases.get(arm.arm().part()));
    }

    /** What a walk names as it meets the forks, kept to the forks it named one way. */
    static final class Gathered {

        private final Map<ModelOccurrence, List<souther.compiler.reading.Condition.Case>> named =
                new LinkedHashMap<>();
        private final Set<ModelOccurrence> namedTwice = new LinkedHashSet<>();

        /** That the arms of {@code fork} are {@code cases}. */
        void name(ModelOccurrence fork, List<souther.compiler.reading.Condition.Case> cases) {
            List<souther.compiler.reading.Condition.Case> before = named.putIfAbsent(fork, cases);
            if (before != null && !before.equals(cases)) {
                namedTwice.add(fork);
            }
        }

        ArmsNamed named() {
            Map<ModelOccurrence, List<souther.compiler.reading.Condition.Case>> out =
                    new LinkedHashMap<>(named);
            out.keySet().removeAll(namedTwice);
            return new ArmsNamed(out);
        }
    }
}
