package souther.compiler.partition;

import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.StatedComparison;
import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.ConstantArguments;
import souther.compiler.semantics.ResultRange;
import souther.compiler.types.ValueName;

import java.util.Optional;

/**
 * Whether a comparison is read back to what the library says it turns on, before it is read as a
 * rule of its own.
 *
 * <p>One case and no more: the size of a container held against a number that parts nought from
 * every size above it, the way the checker reads an emptiness check
 * ({@link souther.compiler.check.BooleanMeaning#asAComparison}), over a container an operation
 * built whose emptiness the library says turns on a closure
 * ({@link souther.compiler.semantics.OperationFact.TurnsOnWhetherAnArgumentHolds}). There, whether
 * the container holds anything is whether some element met the closure, and that is a statement
 * about the input where the size of the container is not: {@code List.filter(p, xs)} is not a
 * position, and its size is a number nothing in the input holds.
 *
 * <p>Which comparisons part nought from the rest is worked out from the relation, not listed.
 * {@code == 0} and {@code /= 0} are the check by the library's own word and need nothing else.
 * An ordering needs where the library says a size starts: a size is a count no lower than nought,
 * so {@code <= 0} and {@code < 1} hold exactly where the container is empty, and {@code > 0} and
 * {@code >= 1} exactly where it is not.
 *
 * <p>Everything else is the comparison's own. A size held against nought over a position is a line
 * on how many it holds; over a value this cannot read back, it is a rule about a value made from the
 * input, which the comparison's reading says. And a size held against a number that parts sizes
 * above nought counts the elements the closure kept, which no answer of the closure states — so
 * {@code List.length(List.filter(p, xs)) >= 2} is a comparison and not read back.
 *
 * <p>The spelling is spent before this is asked. {@code List.isEmpty(ys)} and
 * {@code List.length(ys) == 0} reach here as the one statement, and {@code List.length(ys) >= 1}
 * is read as its denial here, so they are read back alike or none is.
 */
final class WhatAnEmptinessTurnsOn {

    private WhatAnEmptinessTurnsOn() {}

    /**
     * What a comparison says of whether a container holds anything.
     *
     * @param container         the container whose size is held against nought
     * @param emptyWhereItHolds whether the comparison holding is the container holding nothing
     */
    record Checked(Core container, boolean emptyWhereItHolds) {}

    /**
     * A comparison read back to the closure that decides it.
     *
     * @param container what the comparison takes the size of, read where it stands
     * @param decidedBy what the closure deciding whether it holds anything answers with, read where
     *                  it stands
     */
    record ReadBack(Denotation container, Denotation decidedBy) {}

    /**
     * The emptiness {@code stated} checks, or null where it is no size held against a number that
     * parts nought from every size above it.
     */
    static Checked checked(StatedComparison stated) {
        StatedComparison.Numbered<AnOperationApplied> size =
                stated.at(WhatAnEmptinessTurnsOn::aSize);
        if (size == null
                || !(Core.withoutStanding(size.other()) instanceof Core.Int against)) {
            return null;
        }
        Rel relation = size.claim().statedRelation();
        boolean atNought = relation.holds(Long.compare(0, against.value()));
        boolean above = relation.holds(1);
        if (atNought == above) {
            return null;
        }
        // Held equal or unequal to nought, the comparison is the check the library says it means,
        // whatever else is known of the size: it comes out one way at nought and the other way on
        // either side of it.
        boolean noughtAlone = against.value() == 0 && relation.holds(-1) == above;
        return noughtAlone || partsNoughtFromEverySizeAbove(relation, against.value(),
                        size.number().operation())
                ? new Checked(size.number().args().getFirst(), atNought) : null;
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
     * {@code stated} read back to the closure that decides the emptiness it checks — or empty where
     * it is to be read as the comparison it is.
     */
    static Optional<ReadBack> of(StatedComparison stated, WhatNamesStandFor names) {
        Checked checked = checked(stated);
        if (checked == null) {
            return Optional.empty();
        }
        Denotation container = names.standing(checked.container());
        AnOperationApplied built = AnOperationApplied.of(container.value());
        if (built == null) {
            return Optional.empty();
        }
        var turns = DefaultBoundOperationFacts.get()
                .turnsOnWhetherAnArgumentHolds(built.operation(), AnswerAspect.EMPTINESS);
        Core handed = turns == null ? null : built.argument(turns.argument());
        if (handed == null) {
            return Optional.empty();
        }
        Denotation closure = names.in(container.at()).standing(handed);
        return Core.withoutStanding(closure.value()) instanceof Core.Block block
                ? Optional.of(new ReadBack(container, new Denotation(block.body(), closure.at())))
                : Optional.empty();
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
