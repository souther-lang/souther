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
     * @param guard             which {@code if} — by the arms it owns, so a hit set answers whether
     *                          it ran
     * @param valueBelongsBelow which side of the line the cut value itself is on. It decides which
     *                          neighbour is the other class's edge: {@code <= 3000} leaves 3001 over
     *                          there, {@code < 3000} leaves 2999.
     */
    record GuardOrigin(souther.compiler.coverage.CoverageSites.GuardRef guard, SourceRef at,
                       boolean valueBelongsBelow) implements OriginRef {}

    /** Where this came from, for a report to print. */
    default String describe() {
        return switch (this) {
            case TypeOrigin t -> "type " + t.type().name();
            case InvariantOrigin i -> "invariant " + i.type().name() + " (" + i.clause() + ")";
            case GuardOrigin g -> "guard@" + g.at().pos();
        };
    }
}
