package souther.compiler.partition;

import souther.compiler.check.AnOperationApplied;
import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.StatedComparison;
import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReads;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.ConstantArguments;
import souther.compiler.semantics.ResultRange;
import souther.compiler.types.BinOp;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Whether a comparison is a size held against a number that parts nought from every size above it
 * — which is asking whether the container holds anything, however it is spelt.
 *
 * <p>Which comparisons do is worked out from the relation, not listed. {@code == 0} and
 * {@code /= 0} are the check by the library's own word and need nothing else. An ordering needs
 * where the library says a size starts: a size is a count no lower than nought, so {@code <= 0}
 * and {@code < 1} hold exactly where the container is empty, and {@code > 0} and {@code >= 1}
 * exactly where it is not. A size held against a number that parts sizes above nought —
 * {@code >= 2}, {@code == 1} — counts what the container holds and is the comparison it is.
 *
 * <p>The spelling is spent before this is asked. {@code List.isEmpty(ys)} and
 * {@code List.length(ys) == 0} reach here as the one statement ({@link
 * souther.compiler.check.BooleanMeaning#asAComparison}).
 */
final class AnEmptinessCheck {

    private AnEmptinessCheck() {}

    /**
     * What a comparison says of whether containers hold anything.
     *
     * @param containers        the containers whose sizes are added up and held against nought,
     *                          one where a size alone is, each where it is read, each once
     * @param bareSize          whether it is a size alone and not a sum: a size added to itself
     *                          is a sum of one container
     * @param emptyWhereItHolds whether the comparison holding is the containers holding nothing
     * @param written           the comparison with the name its sum was given followed, and the
     *                          reading it is read in: what the arithmetic over the input is
     *                          asked of, to tell a sum it reads from one it does not
     * @param named             whether the sum is a name that was followed to what it stands for
     */
    record Checked(List<Denotation> containers, boolean bareSize, boolean emptyWhereItHolds,
                   StatedComparison written, InputReads writtenAt, boolean named) {

        Checked {
            containers = List.copyOf(containers);
        }

        /** Whether it is a size alone and not a sum. */
        boolean ofOneContainer() {
            return bareSize;
        }
    }

    /** A size, and the reading the container it is the size of is read in. */
    private record Size(AnOperationApplied applied, InputReads at) {}

    /**
     * What a name stands for, in the reading it is read in: the value it is bound to and where
     * that value is read ({@link InputReads#standing}). A size or a sum of sizes that was given a
     * name is the check as much as one written in the comparison.
     */
    @FunctionalInterface
    interface Standing {

        Denotation of(Core e, InputReads reads);
    }

    /**
     * The emptiness {@code stated} checks, read in {@code reads}: of one container where it is a
     * size, of several where it is their sizes added up — or null where it is neither held
     * against a number that parts nought from every size or sum above it.
     *
     * <p>A size is no lower than nought, so a sum of them is nought exactly where every one is and
     * is one or more exactly where some one is: the comparison holds exactly where some container
     * holds something, or exactly where none does. Any other way of combining sizes — taking one
     * from another, weighing one more than the rest — is a relation between them, and is not
     * this.
     *
     * <p>That is what the comparison holds, and it says nothing of what a run works out to get
     * there: a sum works out every size, and what is read as some one of them holding something is
     * a statement about the containers and not an order of evaluation. A comparison read as an
     * emptiness check is carried to the input ({@link Pullback#carriesPast}), and what a run works
     * out before it is asked of the written arithmetic, as it is for a size alone.
     */
    static Checked checked(StatedComparison stated, InputReads reads, Standing standing) {
        Denotation[] stood = {null};
        Core[] side = {null};
        StatedComparison.Numbered<SizesAddedUp> sizes = stated.at(each -> {
            SizesAddedUp out = new SizesAddedUp();
            Denotation followed = standing.of(each, reads);
            if (!addedUp(followed, standing, out)) {
                return null;
            }
            stood[0] = followed;
            side[0] = each;
            return out;
        });
        if (sizes == null
                || !(Core.withoutStanding(standing.of(sizes.other(), reads).value())
                        instanceof Core.Int against)) {
            return null;
        }
        Rel relation = sizes.claim().statedRelation();
        boolean atNought = relation.holds(Long.compare(0, against.value()));
        boolean above = relation.holds(1);
        if (atNought == above) {
            return null;
        }
        // Held equal or unequal to nought, the comparison is the check the library says it means,
        // whatever else is known of the size: it comes out one way at nought and the other way on
        // either side of it.
        boolean noughtAlone = against.value() == 0 && relation.holds(-1) == above;
        if (!noughtAlone && !sizes.number().sizes.stream().allMatch(size ->
                partsNoughtFromEverySizeAbove(relation, against.value(),
                        size.applied().operation()))) {
            return null;
        }
        boolean onTheLeft = side[0] == stated.left();
        StatedComparison written = new StatedComparison(stated.claim(),
                onTheLeft ? stood[0].value() : stated.left(),
                onTheLeft ? stated.right() : stood[0].value(), stated.reading());
        return new Checked(sizes.number().sizes.stream().map(size -> new Denotation(
                size.applied().args().getFirst(), size.at())).toList(), !sizes.number().ofASum,
                atNought, written, stood[0].at(),
                Core.withoutStanding(stood[0].value()) != Core.withoutStanding(side[0]));
    }

    /**
     * Whether {@code e} is sizes and nothing else added together, the sizes put in {@code into}
     * in the order they are added.
     */
    private static boolean addedUp(Denotation e, Standing standing, SizesAddedUp into) {
        Core value = Core.withoutStanding(e.value());
        if (!into.visited.add(new Visited(value, e.at()))) {
            return true;
        }
        if (value instanceof Core.Binary sum && sum.op() == BinOp.ADD) {
            into.ofASum = true;
            return addedUp(standing.of(sum.left(), e.at()), standing, into)
                    && addedUp(standing.of(sum.right(), e.at()), standing, into);
        }
        AnOperationApplied size = aSize(e.value());
        return size != null && into.sizes.add(new Size(size, e.at()));
    }

    /**
     * The sizes an expression adds up, each once however many ways lead to it, in the order they
     * are first added; and whether it is a sum at all.
     *
     * <p>A name used twice in a sum stands for one value, and a chain of such sums reaches a size
     * by a number of ways that doubles with each link. Each value is taken once in the reading it
     * is read in, so the work and what it holds follow the values and not the ways to them. A sum
     * is nought exactly where every size is, and is one or more exactly where some one is, so how
     * many times a size is added is not asked of it.
     */
    private static final class SizesAddedUp {
        private final Set<Visited> visited = new HashSet<>();
        private final List<Size> sizes = new ArrayList<>();
        private boolean ofASum;
    }

    /** A value, by what object it is, in the reading it is read in. */
    private record Visited(Core value, InputReads at) {

        @Override
        public boolean equals(Object other) {
            return other instanceof Visited that && that.value == value && that.at.equals(at);
        }

        @Override
        public int hashCode() {
            return 31 * System.identityHashCode(value) + at.hashCode();
        }
    }

    /**
     * Whether {@code relation} against {@code against} comes out the same at every size above
     * nought, where {@code operation} answers no size below it.
     *
     * <p>Only there does an ordering part nought from the rest: {@code >= 1} is {@code /= 0} for
     * a count and for nothing that can be negative. Above nought a size is one or more. Far enough
     * above, every size is above what it is held against; nearer, it may stand at it or below it,
     * and the comparison has to come out the same there too.
     */
    private static boolean partsNoughtFromEverySizeAbove(Rel relation, long against,
                                                        ValueName operation) {
        boolean above = relation.holds(1);
        return (against < 1 || relation.holds(0) == above)
                && (against < 2 || relation.holds(-1) == above)
                && startsAtNought(operation);
    }

    /**
     * Whether the least a size {@code operation} answers is nought, as the library bounds its
     * result — the one value an emptiness check is the size standing at.
     */
    private static boolean startsAtNought(ValueName operation) {
        Endpoint least = ResultRange.of(DefaultBoundOperationFacts.get().boundsOnTheResult(operation),
                ConstantArguments.none()).min();
        return least != null && least.inclusive() && least.at().compareTo(Count.ZERO) == 0;
    }

    /**
     * {@code e} as the size of the one container it is handed, or null where it is no size an
     * emptiness check is read as.
     *
     * <p>Which operations those are is the library's: the sizes its emptiness checks mean, and no
     * others.
     */
    private static AnOperationApplied aSize(Core e) {
        AnOperationApplied applied = AnOperationApplied.of(e);
        if (applied == null || applied.args().size() != 1) {
            return null;
        }
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        for (ValueName check : facts.meansTheSameAsASizeOfNought()) {
            if (facts.meansTheSameAsASizeOfNought(check).size().operation()
                    .equals(applied.operation())) {
                return applied;
            }
        }
        return null;
    }
}
