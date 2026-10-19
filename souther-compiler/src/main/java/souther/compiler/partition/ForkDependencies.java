package souther.compiler.partition;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.PositionsAStatementReads;
import souther.compiler.meaning.Proposition;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.Collections;
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
 * <p>Two questions keyed on constructs of the model ({@link ModelOccurrence}), and held apart
 * because one construct can be asked both: what the condition of a fork the model wrote reads, and
 * what the answer of a closure's body reads where an operation's fork is decided by it. A closure
 * whose body is an {@code if} is both, and its condition reads less than the whole body. One
 * construct read in more than one place is read the same way in each, and the positions of all of
 * them are what it may turn on.
 *
 * @param byFork   what the condition of each fork the model wrote reads
 * @param byAnswer what the answer of each closure body, by the construct it answers with, reads
 * @param statedByFork the statement the condition of a fork the model wrote makes, where every
 *                 reading of it came to one statement
 * @param applied  every application a run makes of the closure whose body is decided by the
 *                 construct, in the order they were read: what each states and what it takes to
 *                 make it. Absent for a closure whose applications are not all said
 */
public record ForkDependencies(Map<ModelOccurrence, Dependency> byFork,
                               Map<ModelOccurrence, Dependency> byAnswer,
                               Map<ModelOccurrence, Proposition> statedByFork,
                               Map<ModelOccurrence, List<Application>> applied) {

    public static final ForkDependencies NONE =
            new ForkDependencies(Map.of(), Map.of(), Map.of(), Map.of());

    public ForkDependencies {
        byFork = Map.copyOf(byFork);
        byAnswer = Map.copyOf(byAnswer);
        statedByFork = Map.copyOf(statedByFork);
        Map<ModelOccurrence, List<Application>> copied = new LinkedHashMap<>();
        applied.forEach((answers, each) -> copied.put(answers, List.copyOf(each)));
        applied = Collections.unmodifiableMap(copied);
    }

    /**
     * One application of a closure.
     *
     * @param stated  what the closure's body states on it
     * @param reached what has to hold for a run to make it
     */
    public record Application(Proposition stated, Proposition reached) {}

    /** Every application made of the closure the construct {@code answers} decides the body of,
     *  or empty where they are not all said. */
    public Optional<List<Application>> appliedAt(ModelOccurrence answers) {
        return Optional.ofNullable(applied.get(answers));
    }

    /** What the condition of {@code fork} states, or empty where it was read to no one statement. */
    public Optional<Proposition> statedBy(ModelOccurrence fork) {
        return Optional.ofNullable(statedByFork.get(fork));
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
    }

    /** What the condition of {@code fork} may turn on, or empty where nothing read it. */
    public Optional<Dependency> ofTheFork(ModelOccurrence fork) {
        return Optional.ofNullable(byFork.get(fork));
    }

    /** What the answer {@code answers} gives may turn on, or empty where nothing read it. */
    public Optional<Dependency> ofTheAnswer(ModelOccurrence answers) {
        return Optional.ofNullable(byAnswer.get(answers));
    }

    /** What a walk reads as it meets the constructs that decide forks. */
    static final class Gathered {

        private final Bounds forks = new Bounds(true);
        private final Bounds answers = new Bounds(false);
        private final Map<ModelOccurrence, List<Application>> applications =
                new LinkedHashMap<>();
        private final Set<ModelOccurrence> applicationsNotSaid = new LinkedHashSet<>();

        /** That the condition of {@code fork} states {@code stated}, wherever else it was read. */
        void forkReads(ModelOccurrence fork, Proposition stated) {
            forks.reads(fork, stated);
        }

        /** That the answer {@code answers} gives states {@code stated} on one application. */
        void answerReads(ModelOccurrence answers, Proposition stated) {
            this.answers.reads(answers, stated);
        }

        /** That nothing bounds what the answer {@code answers} gives may turn on. */
        void answerUnbounded(ModelOccurrence answers) {
            this.answers.unknown.add(answers);
            applicationsNotSaid.add(answers);
        }

        /** That the applications of the closure {@code answers} decides are not all said. */
        void appliedNotSaid(ModelOccurrence answers) {
            applicationsNotSaid.add(answers);
        }

        /** That the closure body decided by {@code answers} is applied once more, as this. */
        void applied(ModelOccurrence answers, Proposition stated, Proposition reached) {
            applications.computeIfAbsent(answers, _ -> new ArrayList<>())
                    .add(new Application(stated, reached));
        }

        ForkDependencies read() {
            Map<ModelOccurrence, List<Application>> said = new LinkedHashMap<>(applications);
            said.keySet().removeAll(applicationsNotSaid);
            return new ForkDependencies(forks.read(), answers.read(), forks.statements(), said);
        }
    }

    /** One question's positions, by construct, with the constructs nothing bounds. */
    private static final class Bounds {

        private final Map<ModelOccurrence, Set<TermPath>> known = new LinkedHashMap<>();
        private final Set<ModelOccurrence> unknown = new LinkedHashSet<>();
        private final Map<ModelOccurrence, Proposition> statements = new LinkedHashMap<>();
        private final Set<ModelOccurrence> readTwoWays = new LinkedHashSet<>();
        private final boolean keepsStatements;

        /** @param keepsStatements whether the statements are asked for, and so held beside the
         *                         positions */
        Bounds(boolean keepsStatements) {
            this.keepsStatements = keepsStatements;
        }

        void reads(ModelOccurrence decides, Proposition stated) {
            if (keepsStatements) {
                Proposition before = statements.putIfAbsent(decides, stated);
                if (before != null && before != stated && !before.equals(stated)) {
                    readTwoWays.add(decides);
                }
            }
            Optional<List<TermPath>> positions = PositionsAStatementReads.of(stated);
            if (positions.isEmpty()) {
                unknown.add(decides);
                return;
            }
            known.computeIfAbsent(decides, _ -> new LinkedHashSet<>()).addAll(positions.get());
        }

        /** What each construct states, where every reading of it came to the same statement. */
        Map<ModelOccurrence, Proposition> statements() {
            Map<ModelOccurrence, Proposition> out = new LinkedHashMap<>(statements);
            out.keySet().removeAll(readTwoWays);
            return out;
        }

        Map<ModelOccurrence, Dependency> read() {
            Map<ModelOccurrence, Dependency> out = new LinkedHashMap<>();
            known.forEach((decides, positions) ->
                    out.put(decides, new Dependency.Known(List.copyOf(positions))));
            unknown.forEach(decides -> out.put(decides, new Dependency.Unknown()));
            return out;
        }
    }
}
