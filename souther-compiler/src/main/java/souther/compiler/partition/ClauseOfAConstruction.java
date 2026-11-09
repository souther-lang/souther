package souther.compiler.partition;

import souther.compiler.check.Clause;

import java.util.Objects;

/**
 * Which clause of an invariant what a run getting past a construction states is about: a clause of
 * the type it builds, or none, where a declaration whose clauses govern the value was not reached.
 *
 * <p>Two answers, and a reader of a construction a way goes through is told which it holds. Where
 * the declaration was not reached, what getting past the construction states is that the invariant
 * was not read — an unread statement, which states nothing of the input. So no proof that no input
 * gets past a way rests on it: a region cannot take in what was not read, and a proof had with it is
 * had without it. A way whose least proof keeps a construction of this kind alone is therefore never
 * one every run of which stops ({@link DecisionReading.EveryRunStops}); it is kept only where the
 * figure of conditions taken in left the proof without it unanswered
 * ({@link DecisionReading.UndecidedAtAFigure}).
 */
public sealed interface ClauseOfAConstruction {

    /**
     * A clause of the invariant of the type the construction builds.
     *
     * @param clause the clause, by the declaration that wrote it and its place among its clauses
     */
    record Held(Clause.Ref clause) implements ClauseOfAConstruction {

        public Held {
            Objects.requireNonNull(clause, "a clause held to is some clause");
        }
    }

    /** No clause: a declaration whose clauses govern the value was not reached, and what is
     *  stated is that the invariant was not read. */
    record NotReached() implements ClauseOfAConstruction {}
}
