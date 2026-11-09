package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.SequencedMap;
import java.util.function.Function;

/**
 * A relation among how many elements of one container meet statements, and how many that container
 * holds.
 *
 * <p>Every quantity in it is settled by the same elements: which statements each of them meets, and
 * how many there are. None is a number a row writes at a place of its own, which is why a reader
 * taking a relation to be one count and numbers of the input beside it has no place for the rest.
 * Held apart from every reader so that each asks the one question the one way: whether a relation
 * is of this kind is {@link #in}, what it comes to for a container holding so many is
 * {@link #holdsAt}, and whether it can still come to that while some elements are not yet shared
 * out is {@link #mayHoldWith}.
 *
 * <p>Of one container only. The size of a container is the count of the elements meeting what every
 * element meets, so a relation over the counts and the size of a single container is a relation
 * over one set of elements; a count of another container's elements, or a number a row writes, is
 * not settled by them.
 *
 * @param container  the container every count is of, and whose size is weighed where it is
 * @param counts     each count and what it is weighed by, in the order {@link #holdsAt} reads
 * @param sizeWeight what the container's size is weighed by, nought where it is not weighed
 * @param constant   what is added to the sum
 * @param rel        the relation the sum holds to nought
 */
record AggregateRelation(TermPath container, SequencedMap<Quantity.HowManyMeet, ExactRatio> counts,
                         ExactRatio sizeWeight, ExactRatio constant, Rel rel) {

    /** The most counts a relation is composed for: every sharing of the elements among the ways
     *  they meet the counts is walked, and there are more of them with each count. */
    private static final int MOST_COUNTS = 2;

    AggregateRelation {
        Objects.requireNonNull(container, "a relation over the elements of some container");
        Objects.requireNonNull(sizeWeight, "what the size is weighed by, or nought");
        Objects.requireNonNull(constant, "what is added to the sum");
        Objects.requireNonNull(rel, "a relation the sum holds to nought");
        if (counts.isEmpty()) {
            throw new IllegalArgumentException("a relation among counts weighs a count");
        }
        counts = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(counts));
    }

    /**
     * What {@code compared} comes to as a relation among counts of one container and its size, or
     * null where it is none: where it weighs anything but those, or counts of two containers, or no
     * count, or one count beside nothing — which is a count against a number.
     *
     * @param sizeOf the term that names how many the container at a position holds, or null where
     *               its type measures none
     */
    static AggregateRelation in(Relation.Affine affine, boolean holds,
                                Function<TermPath, NumericTerm> sizeOf) {
        SequencedMap<Quantity.HowManyMeet, ExactRatio> counts = new LinkedHashMap<>();
        TermPath container = null;
        for (Map.Entry<Quantity, ExactRatio> each : affine.form().coefs().entrySet()) {
            if (each.getKey() instanceof Quantity.HowManyMeet count
                    && count.container() instanceof DecisionSubject.AnInput(TermPath at, var _)
                    && (container == null || container.equals(at))) {
                container = at;
                counts.put(count, each.getValue());
            } else if (!(each.getKey() instanceof DecisionAtom.OfTheInput(NumericTerm _, var _))) {
                return null;
            }
        }
        if (container == null) {
            return null;
        }
        NumericTerm size = sizeOf.apply(container);
        ExactRatio sizeWeight = ExactRatio.ZERO;
        for (Map.Entry<Quantity, ExactRatio> each : affine.form().coefs().entrySet()) {
            if (each.getKey() instanceof DecisionAtom.OfTheInput(NumericTerm term, var _)) {
                if (size == null || !term.equals(size)) {
                    return null;
                }
                sizeWeight = each.getValue();
            }
        }
        if (counts.size() == 1 && sizeWeight.signum() == 0) {
            return null;
        }
        Rel rel = holds ? affine.proposition() : affine.proposition().denied();
        return new AggregateRelation(container, counts, sizeWeight, affine.form().constant(), rel);
    }

    /**
     * Whether the relation holds of a container of {@code size} elements of which {@code meeting}
     * meet what each count counts, in the order of {@link #counts}.
     */
    ExactAnswer<Boolean> holdsAt(int size, int[] meeting) {
        return valueAt(size, meeting).map(total -> rel.holds(total.signum()));
    }

    /**
     * Whether the relation may hold of a container of {@code size} elements of which at least
     * {@code least} and at most {@code most} meet what each count counts: whether the sum, which
     * is no further from nought than the ends of what it can be, may stand the way the relation
     * asks. Where an end is no number an exact ratio holds, it may.
     */
    boolean mayHoldWith(int size, int[] least, int[] most) {
        int[] low = new int[least.length];
        int[] high = new int[least.length];
        int at = 0;
        for (ExactRatio weight : counts.values()) {
            boolean up = weight.signum() > 0;
            low[at] = up ? least[at] : most[at];
            high[at] = up ? most[at] : least[at];
            at++;
        }
        if (!(valueAt(size, low) instanceof ExactAnswer.Held<ExactRatio>(ExactRatio smallest))
                || !(valueAt(size, high) instanceof ExactAnswer.Held<ExactRatio>(
                        ExactRatio largest))) {
            return true;
        }
        return switch (rel) {
            case GE -> largest.signum() >= 0;
            case GT -> largest.signum() > 0;
            case LE -> smallest.signum() <= 0;
            case LT -> smallest.signum() < 0;
            case EQ -> smallest.signum() <= 0 && largest.signum() >= 0;
            case NE -> smallest.signum() != 0 || largest.signum() != 0;
        };
    }

    /**
     * The fewest elements of each count's statement a container of at most {@code most} elements
     * can have where the relation holds, taking the first count's fewest before the second's, in
     * the order of {@link #counts} — or null where no container that large holds it, and where
     * more counts are weighed than a container is composed for.
     *
     * <p>A figure of the walk and not of the relation: a container with more elements may hold it
     * where none with so many does, so null is what composing reaches and no answer about the
     * relation.
     */
    int[] fewestWithin(int most) {
        int[] meeting = new int[counts.size()];
        return meeting.length <= MOST_COUNTS && fewest(meeting, 0, most) ? meeting : null;
    }

    private boolean fewest(int[] meeting, int at, int most) {
        if (at == meeting.length) {
            int largest = 0;
            for (int each : meeting) {
                largest = Math.max(largest, each);
            }
            for (int size = largest; size <= most; size++) {
                if (holdsAt(size, meeting) instanceof ExactAnswer.Held<Boolean>(Boolean holds)
                        && holds) {
                    return true;
                }
            }
            return false;
        }
        for (int n = 0; n <= most; n++) {
            meeting[at] = n;
            if (fewest(meeting, at + 1, most)) {
                return true;
            }
        }
        return false;
    }

    /** The statements counted, in the order of {@link #counts}. */
    List<Quantity.HowManyMeet> counted() {
        return new ArrayList<>(counts.keySet());
    }

    private ExactAnswer<ExactRatio> valueAt(int size, int[] meeting) {
        ExactAnswer<ExactRatio> sum = sizeWeight.times(ExactRatio.of(size))
                .flatMap(weighed -> weighed.plus(constant));
        int at = 0;
        for (ExactRatio weight : counts.values()) {
            int n = meeting[at++];
            sum = sum.flatMap(so -> weight.times(ExactRatio.of(n)).flatMap(so::plus));
        }
        return sum;
    }
}
