package souther.compiler.partition;

import souther.compiler.inputs.TermPath;
import souther.compiler.types.ModelOccurrence;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * What each arm of a fork is about, as the tree the language's own operations stand in reads the
 * fork.
 *
 * <p>For the arms the reading of the runs could not name. That reading walks the tree where an
 * operation handing a closure the elements of a container is expanded, so a name the closure is
 * handed stands for no position there and an arm on it is a
 * {@link souther.compiler.reading.Condition.Arm} with no subject — and so is an arm of an
 * {@code if} on what such an operation answers. Where the operation still stands, the name is the
 * element it was handed, and the arm is a case of that element; and what the operation answers is
 * a statement about the container, which reads the positions it names and no other.
 *
 * <p>Joined on the construct of the model the two readings agree about ({@link ModelOccurrence}),
 * which is what the readings of the comparisons are joined on as well. A construct the second
 * reading met at more than one position names none of them.
 *
 * @param byFork  the cases of each {@code match}'s arms, in the order of its arms
 * @param readsOf the positions of the input what each {@code if} turns on reads, where it reads
 *                nothing else
 */
public record ArmsNamed(
        Map<ModelOccurrence, List<souther.compiler.reading.Condition.Case>> byFork,
        Map<ModelOccurrence, List<TermPath>> readsOf) {

    public static final ArmsNamed NONE = new ArmsNamed(Map.of(), Map.of());

    public ArmsNamed {
        Map<ModelOccurrence, List<souther.compiler.reading.Condition.Case>> copied =
                new LinkedHashMap<>();
        byFork.forEach((fork, cases) -> copied.put(fork, List.copyOf(cases)));
        byFork = Map.copyOf(copied);
        Map<ModelOccurrence, List<TermPath>> read = new LinkedHashMap<>();
        readsOf.forEach((fork, positions) -> read.put(fork, List.copyOf(positions)));
        readsOf = Map.copyOf(read);
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

    /** The positions what {@code arm}'s fork turns on reads, or empty where nothing said which. */
    public Optional<List<TermPath>> reads(souther.compiler.reading.Condition.Arm arm) {
        return ModelOccurrence.statedAt(arm.arm().fork()).map(readsOf::get);
    }

    /** What a walk names as it meets the forks, kept to the forks it named one way. */
    static final class Gathered {

        private final Map<ModelOccurrence, List<souther.compiler.reading.Condition.Case>> named =
                new LinkedHashMap<>();
        private final Map<ModelOccurrence, List<TermPath>> read = new LinkedHashMap<>();
        private final Set<ModelOccurrence> namedTwice = new LinkedHashSet<>();

        /** That the arms of {@code fork} are {@code cases}. */
        void name(ModelOccurrence fork, List<souther.compiler.reading.Condition.Case> cases) {
            List<souther.compiler.reading.Condition.Case> before = named.putIfAbsent(fork, cases);
            if (before != null && !before.equals(cases)) {
                namedTwice.add(fork);
            }
        }

        /** That what {@code fork} turns on reads {@code positions}, or something else as well
         *  where empty. */
        void reads(ModelOccurrence fork, Optional<List<TermPath>> positions) {
            if (positions.isEmpty()) {
                namedTwice.add(fork);
                return;
            }
            List<TermPath> before = read.putIfAbsent(fork, positions.get());
            if (before != null && !before.equals(positions.get())) {
                namedTwice.add(fork);
            }
        }

        ArmsNamed named() {
            Map<ModelOccurrence, List<souther.compiler.reading.Condition.Case>> out =
                    new LinkedHashMap<>(named);
            out.keySet().removeAll(namedTwice);
            Map<ModelOccurrence, List<TermPath>> reads = new LinkedHashMap<>(read);
            reads.keySet().removeAll(namedTwice);
            return new ArmsNamed(out, reads);
        }
    }
}
