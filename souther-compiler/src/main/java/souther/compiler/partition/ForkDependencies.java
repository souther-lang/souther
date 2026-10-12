package souther.compiler.partition;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.PositionsAStatementReads;
import souther.compiler.meaning.Proposition;
import souther.compiler.types.ModelOccurrence;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * Which positions of the input a fork may turn on, as the tree the language's own operations stand
 * in reads what decides it.
 *
 * <p>For the forks the reading of the runs could name no subject for: an {@code if} on what an
 * operation over a container answers, and a fork inside an operation's own body whose condition is
 * a closure the model handed it. Neither stands on a position, and each turns on what a statement
 * the second reading makes reads.
 *
 * <p>An upper bound and not a reading of classes. A fork said to turn on these positions may tell
 * apart any of them and nothing else; which classes go which way is not said, and a reader that
 * puts a fork here puts nothing it says to classes. A statement only part of which was read, or
 * one that reads an answer or a value the body bound, may turn on anything: that is
 * {@link Dependency.Unknown}, never the part that was read.
 *
 * <p>Keyed on the construct of the model that decides: the fork where the model wrote it, and the
 * statement a closure answers with where the fork is the operation's ({@link ModelOccurrence}). One
 * construct read in more than one place is read the same way in each, and the positions of all of
 * them are what it may turn on.
 *
 * @param byConstruct what each construct that decides a fork may turn on
 */
public record ForkDependencies(Map<ModelOccurrence, Dependency> byConstruct) {

    public static final ForkDependencies NONE = new ForkDependencies(Map.of());

    public ForkDependencies {
        byConstruct = Map.copyOf(byConstruct);
    }

    /** What a construct that decides a fork may turn on. */
    public sealed interface Dependency {

        /** These positions and no other: none where it turns on nothing of the input. */
        record Known(List<TermPath> positions) implements Dependency {

            public Known {
                positions = List.copyOf(positions);
            }
        }

        /** Positions nothing here could bound. */
        record Unknown() implements Dependency {}

        /** What {@code stated} reads, as a dependency. */
        static Dependency of(Proposition stated) {
            return PositionsAStatementReads.of(stated)
                    .<Dependency>map(Known::new).orElseGet(Unknown::new);
        }
    }

    /** What {@code decides} may turn on, or empty where nothing read it. */
    public Optional<Dependency> of(ModelOccurrence decides) {
        return Optional.ofNullable(byConstruct.get(decides));
    }

    /** What a walk reads as it meets the constructs that decide forks. */
    static final class Gathered {

        private final Map<ModelOccurrence, Set<TermPath>> known = new LinkedHashMap<>();
        private final Set<ModelOccurrence> unknown = new LinkedHashSet<>();

        /** That {@code decides} may turn on what {@code stated} reads, wherever else it was read. */
        void reads(ModelOccurrence decides, Proposition stated) {
            switch (Dependency.of(stated)) {
                case Dependency.Known(var positions) ->
                        known.computeIfAbsent(decides, _ -> new LinkedHashSet<>())
                                .addAll(positions);
                case Dependency.Unknown _ -> unknown.add(decides);
            }
        }

        /** That nothing bounds what {@code decides} may turn on. */
        void unbounded(ModelOccurrence decides) {
            unknown.add(decides);
        }

        ForkDependencies read() {
            Map<ModelOccurrence, Dependency> out = new LinkedHashMap<>();
            known.forEach((decides, positions) ->
                    out.put(decides, new Dependency.Known(List.copyOf(positions))));
            unknown.forEach(decides -> out.put(decides, new Dependency.Unknown()));
            return new ForkDependencies(out);
        }
    }
}
