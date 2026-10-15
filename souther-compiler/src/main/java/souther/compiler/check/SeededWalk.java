package souther.compiler.check;

import souther.compiler.core.Core;

import java.util.function.Function;

/**
 * A call of an operation that walks a container from a seed ({@link Reductions}), with the parts a
 * reader of what it answers needs: the seed, the container, the step and the two parameters of it.
 *
 * <p>What the step does with them is not said here. That it answers the seed or the step applied to
 * an earlier answer and an element is all {@link Reductions} licenses, and what a reader makes of
 * the answer beyond that is read off the step.
 *
 * @param seed        what the walk starts from
 * @param container   what the walk walks
 * @param step        the closure the walk repeats
 * @param accumulator the parameter of the step the answer so far arrives on
 * @param element     the parameter of the step an element of the container arrives on
 */
public record SeededWalk(Core seed, Core container, Core.Block step, Core.Binder accumulator,
                         Core.Binder element) {

    /**
     * What {@code node} is, where it is a call of a walk from a seed whose step is a block with both
     * its parameters named, or null where it is anything else.
     *
     * @param blockOf the block a closure argument stands for, where the call stands
     */
    public static SeededWalk of(Core node, Function<Core, Core.Block> blockOf) {
        if (!(Core.withoutStanding(node) instanceof Core.PreservedCall call)) {
            return null;
        }
        Reductions.Reducing walk = Reductions.reducing(call, blockOf);
        return walk == null || walk.element() == null || walk.element().binding() == null
                || walk.accumulator() == null || walk.accumulator().binding() == null
                ? null : new SeededWalk(walk.seed(), walk.container(), walk.step(),
                        walk.accumulator(), walk.element());
    }
}
