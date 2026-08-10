package souther.compiler.partition;

import souther.compiler.diag.SourceRef;
import souther.compiler.types.TypeName;

import java.util.Optional;

/**
 * Where a partition or a boundary came from.
 *
 * <p>Kept per cut rather than per axis. Several rules can put a cut at the same value — a type's
 * invariant and a {@code guard} that repeats it, or two guards written in different behaviors — and
 * they merge into one partition while staying separate obligations. Reaching the boundary through one
 * guard says nothing about the other.
 */
public sealed interface OriginRef {

    /** The cases of a sum, or the two values of a {@code Bool}: the type itself says the partition. */
    record TypeOrigin(TypeName type) implements OriginRef {}

    /**
     * A clause of a {@code data}'s invariant.
     *
     * @param at empty for a type that arrived from a module compiled elsewhere, whose clause has no
     *           position in this compilation
     */
    record InvariantOrigin(Optional<SourceRef> at, TypeName type, String clause)
            implements OriginRef {

        public InvariantOrigin {
            at = at == null ? Optional.empty() : at;
        }
    }

    /**
     * A comparison in a behavior's body, and the {@code if} it is the condition of.
     *
     * <p>The guard is kept, not just the position, because meeting this boundary takes more than
     * writing the value: the comparison has to have been evaluated. A row can hand the behavior the
     * exact threshold and never reach the guard that cares about it.
     *
     * @param guard             which {@code if} — by the arms it owns, which is what says which
     *                          class of the partition a row landed in
     * @param site              where the comparison's own value is recorded. Required, and this is
     *                          what meeting the line is measured against: a row met it by getting the
     *                          comparison to answer, which is not what any arm records. A condition
     *                          stops as soon as it is settled, so under {@code A && B} the arm where
     *                          the condition failed holds rows that made {@code B} false and rows
     *                          that never reached {@code B}
     * @param valueBelongsBelow which side of the line the cut value itself is on. It decides which
     *                          neighbour is the other class's edge: {@code <= 3000} leaves 3001 over
     *                          there, {@code < 3000} leaves 2999.
     * @param witness           which arms of the {@code if} a row reaching this comparison can land
     *                          in. Not what says the comparison ran — {@code site} is — but what says
     *                          which arm's edge is this comparison's to draw, which is a question
     *                          about the classes either side of the line
     * @param holdsAtTheValue   whether the comparison is true at the line's own value. Not derivable
     *                          from {@code valueBelongsBelow}: {@code x <= c} and {@code x > c} agree
     *                          about the class the value is in and disagree here
     */
    record GuardOrigin(souther.compiler.coverage.CoverageSites.GuardRef guard, int site,
                       SourceRef at, boolean valueBelongsBelow, Witness witness,
                       boolean holdsAtTheValue, boolean singles) implements OriginRef {

        public GuardOrigin(souther.compiler.coverage.CoverageSites.GuardRef guard, int site,
                           SourceRef at, boolean valueBelongsBelow, Witness witness,
                           boolean holdsAtTheValue) {
            this(guard, site, at, valueBelongsBelow, witness, holdsAtTheValue, false);
        }

        /** Which arms a row that reached this comparison can be in. */
        public enum Witness {
            /** Either: the comparison is on the leftmost spine, so it runs whatever the condition
             * comes to. */
            BOTH,
            /** Only the arm the whole condition is true on, which is a conjunction. */
            THEN,
            /** Only the arm it is false on, which is a disjunction. */
            ELSE,
            /** Neither on its own, which a condition mixing {@code &&} and {@code ||} leaves: a row
             * that reached the comparison can be in either arm, so neither arm's edge is this
             * comparison's alone. */
            NEITHER
        }
    }

    /**
     * A bound one rule put there and another took in.
     *
     * <p>One obligation and not two. The rules do not each want a row: {@code MinuteOfDay}'s maximum
     * is why this position has an upper edge at all, and {@code WorkInterval}'s clause is why that
     * edge is 1439 rather than 1440. Kept as two origins side by side they would be counted as two
     * boundaries at one value, which is the accounting for rules that each drew a line of their own
     * — an invariant and a guard naming the same number — and not for one line two rules settled
     * together.
     *
     * @param bound  the rule that put an edge here
     * @param within the record whose own clauses decided where it stopped
     */
    record NarrowedOrigin(OriginRef bound, TypeName within) implements OriginRef {}

    /** Where this came from, for a report to print. */
    default String describe() {
        return switch (this) {
            case TypeOrigin t -> "type " + t.type().name();
            case InvariantOrigin i -> "invariant " + i.type().name() + " (" + i.clause() + ")";
            case GuardOrigin g -> "guard@" + g.at().pos();
            case NarrowedOrigin n -> n.bound().describe() + " within " + n.within().name();
        };
    }
}
