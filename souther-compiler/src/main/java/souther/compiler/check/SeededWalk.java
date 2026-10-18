package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.core.WhatABodyReads;
import souther.compiler.types.BindingId;

import java.util.function.Function;

/**
 * A call of an operation that walks a container from a seed ({@link Reductions}), with the parts a
 * reader of what it answers needs: the seed, the container, the step and the two parameters of it.
 *
 * <p>That it answers the seed or the step applied to an earlier answer and an element is all
 * {@link Reductions} licenses, and what a reader makes of the answer beyond that is read off the
 * step. Which end of two values the step keeps is read here ({@link #endKept}), because it is a
 * question about the step alone.
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

    /**
     * The end the step keeps of the answer so far and one value it reads of the element alone.
     *
     * @param extreme which end of the two the step answers
     * @param value   the other of the two, which reads nothing of the answer so far
     */
    public record AnEndKept(Extreme extreme, Core value) {}

    /**
     * The end this walk's step keeps, where the step answers the answer so far or one value of the
     * element by how the two stand, and always the same end of them ({@link Extreme#keptBy}) — or
     * null where it answers anything else.
     *
     * <p>Such a step answers the greater or the lesser of what it was carried and that value, so by
     * induction over the walk what the walk ends with is that end of the seed and the value on
     * every element. {@code if l.discount > w then l.discount else w} and
     * {@code Int.max(w, l.discount)} keep the greater of {@code w} and {@code l.discount}; a step
     * that adds to what it chose, or chooses by anything but how the two stand, keeps neither.
     *
     * <p>A newtype's value read off either of the two is that one where the step compares them
     * ({@link #opened}), so a step comparing {@code l.rate.value} with {@code w.value} and
     * answering {@code l.rate} or {@code w} keeps an end of {@code w} and {@code l.rate}.
     */
    public AnEndKept endKept(DeclarationNewtypes newtypes) {
        BindingId carried = accumulator.binding();
        Choice choice = Choice.of(Core.withoutStanding(step.body()));
        if (choice == null) {
            return null;
        }
        Core value = null;
        for (Choice.Arm arm : choice.arms()) {
            if (isTheCarried(arm.answers(), carried)) {
                continue;
            }
            if (value != null && !Core.sameValue(value, arm.answers())) {
                return null;
            }
            value = arm.answers();
        }
        if (value == null || WhatABodyReads.binding(value, carried)) {
            return null;
        }
        Core other = value;
        Extreme extreme = Extreme.keptBy(step.body(),
                e -> isTheCarried(opened(e, newtypes), carried),
                e -> Core.sameValue(opened(e, newtypes), other));
        return extreme == null ? null : new AnEndKept(extreme, value);
    }

    private static boolean isTheCarried(Core e, BindingId carried) {
        return Core.withoutStanding(e) instanceof Core.Read read
                && carried.equals(read.binding());
    }

    /**
     * The value {@code e} reads a newtype's value off, where it does; {@code e} itself otherwise.
     * Reading the value a newtype wears goes nowhere ({@link Location#isStep}), and the two are
     * ordered alike. A projection is asked of its last name, as the access it stands for is.
     */
    public static Core opened(Core e, DeclarationNewtypes newtypes) {
        Core.FieldAccess last = switch (Core.withoutStanding(e)) {
            case Core.FieldAccess access -> access;
            case Core.FieldProjection projection -> projection.lastAccess();
            default -> null;
        };
        return last != null && !Location.isStep(last.target().type(), last.field(), newtypes)
                ? last.target() : e;
    }
}
