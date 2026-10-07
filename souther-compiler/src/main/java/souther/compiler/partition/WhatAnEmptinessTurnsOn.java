package souther.compiler.partition;

import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.StatedComparison;
import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.types.ValueName;

import java.util.Optional;

/**
 * Whether a comparison is read back to what the library says it turns on, before it is read as a
 * rule of its own.
 *
 * <p>One case and no more: the size of a container held equal or unequal to nought, the way the
 * checker reads an emptiness check ({@link souther.compiler.check.BooleanMeaning#asAComparison}),
 * over a container an operation built whose emptiness the library says turns on a closure
 * ({@link souther.compiler.semantics.OperationFact.TurnsOnWhetherAnArgumentHolds}). There, whether
 * the container holds anything is whether some element met the closure, and that is a statement
 * about the input where the size of the container is not: {@code List.filter(p, xs)} is not a
 * position, and its size is a number nothing in the input holds.
 *
 * <p>Everything else is the comparison's own. A size held against nought over a position is a line
 * on how many it holds; over a value this cannot read back, it is a rule about a value made from the
 * input, which the comparison's reading says. And a size held against any other number counts the
 * elements the closure kept, which no answer of the closure states — so {@code List.length(
 * List.filter(p, xs)) >= 2} is a comparison and not read back.
 *
 * <p>The spelling is spent before this is asked. {@code List.isEmpty(ys)} and
 * {@code List.length(ys) == 0} reach here as the one statement, so the two are read back alike or
 * neither is.
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
     * The emptiness {@code stated} checks, or null where it is no size held equal or unequal to
     * nought.
     */
    static Checked checked(StatedComparison stated) {
        StatedComparison.Numbered<Core> size = stated.at(WhatAnEmptinessTurnsOn::sizedContainer);
        if (size == null
                || !(Core.withoutStanding(size.other()) instanceof Core.Int nought)
                || nought.value() != 0) {
            return null;
        }
        Rel relation = size.claim().statedRelation();
        return switch (relation) {
            case EQ -> new Checked(size.number(), true);
            case NE -> new Checked(size.number(), false);
            case GE, GT, LE, LT -> null;
        };
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
     * The container {@code e} takes the size of, or null where it is no size an emptiness check is
     * read as.
     *
     * <p>Which operations those are is the library's: the sizes its emptiness checks mean, and no
     * others.
     */
    private static Core sizedContainer(Core e) {
        AnOperationApplied applied = AnOperationApplied.of(e);
        if (applied == null || applied.args().size() != 1) {
            return null;
        }
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        for (ValueName check : facts.meansTheSameAsASizeOfNought()) {
            if (facts.meansTheSameAsASizeOfNought(check).size().operation()
                    .equals(applied.operation())) {
                return applied.args().getFirst();
            }
        }
        return null;
    }
}
