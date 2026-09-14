package souther.compiler.partition;

import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.AlignedObservation;

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
        if (claims.isEmpty()) {
            // A combination of a body's decisions is decisions being settled, so a run that filled
            // one did something. Allowed to be empty, this would be a combination every run
            // certifies — including one that did nothing — and a claim dropped upstream would come
            // back not as a combination nothing can witness but as one everything does.
            throw new IllegalArgumentException(
                    "a combination of decisions is something a run can be held to");
        }
    }

    /**
     * What {@code seen} did not do of what this names.
     *
     * <p>Empty is the certification. Which of them were missed is kept rather than reduced to
     * whether any were, because that is what says where the reading and the run parted — a row that
     * never reached the meeting misses the way in, and one that reached it and went the other way
     * misses an outcome, and those are different things to be told.
     */
    public List<ControlClaim> missedBy(AlignedObservation seen) {
        return claims.stream().filter(claim -> !claim.satisfiedBy(seen)).toList();
    }

    /** Whether {@code seen} did everything this names. */
    public boolean certifiedBy(AlignedObservation seen) {
        return claims.stream().allMatch(claim -> claim.satisfiedBy(seen));
    }

    /**
     * The readings of this combination a search may look for a row at, one at a time.
     *
     * <p>What this asks of a row and nothing else: a class apiece at the positions it is about, and
     * nothing said about the rest. Which positions those are, and what the readings of the
     * combination are, is answered here — a caller that worked it out from the classes each position
     * admits would be reading this value's own shape, and would have to be rewritten the day a
     * combination can say something about two positions together that it says about neither alone.
     *
     * <p>The first is every position at the first class it admits, and the rest are counted off from
     * it in a fixed order, so one model offers the same rows twice.
     *
     * <p><b>No bound here.</b> How many readings a search may look at is a fact about that search,
     * and which of these are readings at all is the model's answer rather than this value's: a class
     * apiece that no one value can hold is a combination of names and not a reading. Counted off
     * here, the bound was spent on those before anything asked, and a combination whose first few
     * names cannot be in one value went unanswered with its readings untried.
     *
     * <p>None handed over where a position this is about admits no class at all, which is not a
     * reading that failed but a combination the model does not have.
     */
    public Traversal interpretations(Taking<Interpretation> taking) {
        List<Integer> about = new java.util.ArrayList<>();
        List<List<Integer>> admitted = new java.util.ArrayList<>();
        for (int i = 0; i < cell.allowed().length; i++) {
            if (!cell.narrows(i)) {
                continue;
            }
            List<Integer> here = new java.util.ArrayList<>();
            for (int c = 0; c < cell.allowed()[i].length; c++) {
                if (cell.admits(i, c)) {
                    here.add(c);
                }
            }
            if (here.isEmpty()) {
                return Traversal.EXHAUSTED;
            }
            about.add(i);
            admitted.add(here);
        }
        // Counted up one position at a time, and never counted out. How many readings there are is
        // a number nobody here needs — a caller takes three of them and stops — and asking for it
        // put the whole space inside a machine word: sixty-three positions of two classes apiece
        // overflow it, and a walk that read the total back as a negative one handed nothing over and
        // said it had run out.
        int[] standing = new int[about.size()];
        while (true) {
            java.util.Map<Integer, Integer> pins = new java.util.LinkedHashMap<>();
            for (int p = 0; p < about.size(); p++) {
                pins.put(about.get(p), admitted.get(p).get(standing[p]));
            }
            switch (taking.take(new Interpretation(pins))) {
                case NOT_TAKEN -> {
                    return Traversal.STOPPED;
                }
                case AND_DONE -> {
                    return Traversal.SATISFIED;
                }
                case AND_MORE -> { }
            }
            int carry = 0;
            while (carry < about.size()) {
                standing[carry]++;
                if (standing[carry] < admitted.get(carry).size()) {
                    break;
                }
                standing[carry] = 0;
                carry++;
            }
            if (carry == about.size()) {
                return Traversal.EXHAUSTED;   // the last position came back round to its first
            }
        }
    }

    /**
     * Whether this asks for the same row as {@code other}: the same classes, held to the same run.
     *
     * <p>Asked rather than left to equality. A cell is a flag per class of each position, which is
     * an array — so two of these naming one combination are two values that never compare equal,
     * and a search handed both looks in the same place twice, composes the same candidates against
     * the same rules, and writes down what it came to twice over.
     *
     * <p>Both halves, because either alone is a different question. Two selections over the same
     * classes and different claims are two things a row of those values would have to be seen
     * doing; the same claims over different classes are two places to look for one run.
     */
    public boolean sameAs(CellSelection other) {
        return cell.sameAs(other.cell)
                && new java.util.LinkedHashSet<>(claims)
                        .equals(new java.util.LinkedHashSet<>(other.claims));
    }

    /**
     * The row at {@code where} as a witness that this combination is filled, where {@code seen} says
     * it filled it.
     *
     * <p>The only way there is to make one, and it asks both halves. A row fills a combination by
     * sitting where the combination leaves room and by having been seen doing what it names, and a
     * value that took the second on trust would say a row filled a combination it is not even in.
     * A caller holding one half cannot reach for it, which is what stops the reading that composed
     * a row from being read back as evidence for itself.
     */
    public java.util.Optional<CertifiedWitness> certifying(int[] where, AlignedObservation seen) {
        return cell.holds(where) && certifiedBy(seen)
                ? java.util.Optional.of(new CertifiedWitness(this, where, seen))
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
        private final AlignedObservation seen;

        private CertifiedWitness(CellSelection of, int[] where, AlignedObservation seen) {
            this.of = of;
            this.where = where.clone();
            this.seen = seen;
        }

        /** Which combination this fills. */
        public CellSelection of() {
            return of;
        }

        /** Which class of each position the row sits at. */
        public int[] where() {
            return where.clone();
        }

        /** What the run was seen doing, which is what other combinations are asked of in turn. */
        public AlignedObservation seen() {
            return seen;
        }
    }
}
