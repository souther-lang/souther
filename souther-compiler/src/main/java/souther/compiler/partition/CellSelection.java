package souther.compiler.partition;

import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.Observation;

import java.util.List;

/**
 * One combination of a group, as the classes a row filling it may sit in and as what a row that
 * fills it would be seen to do.
 *
 * <p>Two things and the difference between them is the point. The {@link #cell} is a classification
 * of the search space: it says which classes of each position are still open, which is what a search
 * for values works from and what a written row's values can be read against. The {@link #claims} are
 * a statement about a run — that it took the path to the meeting and settled each factor at the
 * outcome this combination names.
 *
 * <p>The first does not establish the second. Putting a value in the classes the cell allows is what
 * the reading believed would steer a row here, and that belief is a chain of readings: which
 * position a decision is about, which comparison a line was drawn off, which classes a condition
 * leaves open. A row whose values sit in the cell and whose run went somewhere else is exactly what
 * a wrong step anywhere in that chain produces, and it looks like a right one until something asks
 * the run.
 *
 * <p>So nothing here says a row covers this. What sits in the cell is admitted; what did what the
 * claims name is certified; and only the second is evidence about the combination.
 */
public record CellSelection(InteractionCells.Cell cell, List<ControlClaim> claims) {

    public CellSelection {
        claims = List.copyOf(claims);
    }

    /**
     * What {@code seen} did not do of what this names.
     *
     * <p>Empty is the certification. Which of them were missed is kept rather than reduced to
     * whether any were, because that is what says where the reading and the run parted — a row that
     * never reached the meeting misses the way in, and one that reached it and went the other way
     * misses an outcome, and those are different things to be told.
     */
    public List<ControlClaim> missedBy(Observation seen) {
        return claims.stream().filter(claim -> !claim.satisfiedBy(seen)).toList();
    }

    /** Whether {@code seen} did everything this names. */
    public boolean certifiedBy(Observation seen) {
        return claims.stream().allMatch(claim -> claim.satisfiedBy(seen));
    }

    /**
     * The row at {@code where} as a witness that this combination is filled, where {@code seen} says
     * it filled it.
     *
     * <p>The only way there is to make one. That a row fills a combination is the one thing here a
     * reader may act on, and it is a conclusion about a run — so it is a value nothing but this can
     * produce, out of the run itself. A caller holding the classes a row sits in cannot reach for it,
     * which is what stops the reading that composed a row from being read back as evidence for
     * itself.
     */
    public java.util.Optional<CertifiedWitness> certifying(int[] where, Observation seen) {
        return certifiedBy(seen) ? java.util.Optional.of(new CertifiedWitness(this, where))
                : java.util.Optional.empty();
    }

    /**
     * A row seen doing what one combination names.
     *
     * <p>Its own type because what it says is not what its parts say. The classes and the run are
     * both readable elsewhere; that the two together fill a combination is the conclusion, and
     * having it be a value means a reader either has it or does not, rather than deciding it again
     * from whatever it has to hand.
     */
    public static final class CertifiedWitness {

        private final CellSelection of;
        private final int[] where;

        private CertifiedWitness(CellSelection of, int[] where) {
            this.of = of;
            this.where = where.clone();
        }

        /** Which combination this fills. */
        public CellSelection of() {
            return of;
        }

        /** Which class of each position the row sits at. */
        public int[] where() {
            return where.clone();
        }
    }
}
