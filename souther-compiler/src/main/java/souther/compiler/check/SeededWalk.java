package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.core.WhatABodyReads;
import souther.compiler.semantics.HowAClosureIsApplied;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;
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
 * <p>A walk is made only of an operation that applies its step to every element ({@link #of}), so
 * a reader concluding something of every element — that the walk ends with a total of what each
 * adds, with the end kept of every one, or that each was asked what the step asks — holds one
 * that licenses it. That is a fact about the operation proved of its body
 * ({@link HowAClosureIsApplied}), and not one a walk from a seed is by being one. A reader that
 * concludes nothing of which elements the step is applied to, only how a run enters it, asks for
 * a walk however far it applies its step ({@link #enteredHoweverFar}).
 *
 * @param seed        what the walk starts from
 * @param container   what the walk walks
 * @param step        the closure the walk repeats
 * @param accumulator the parameter of the step the answer so far arrives on
 * @param element     the parameter of the step an element of the container arrives on
 * @param applied     how far the operation goes applying the step
 * @param inTheContainersOrder whether the elements arrive at the step in the order the container
 *                    holds them, first to last. A reader that unrolls the walk element by element
 *                    asks it; one concluding something of every element does not need it
 */
public record SeededWalk(Core seed, Core container, Core.Block step, Core.Binder accumulator,
                         Core.Binder element, HowAClosureIsApplied applied,
                         boolean inTheContainersOrder) {

    /**
     * What {@code node} is, where it is a call of a walk from a seed whose step is a block with both
     * its parameters named and is applied to every element of the container, each in turn whatever
     * an application answers — or null where it is anything else, or a walk that may stop short or
     * pass some by.
     *
     * @param blockOf the block a closure argument stands for, where the call stands
     */
    public static SeededWalk of(Core node, Function<Core, Core.Block> blockOf) {
        SeededWalk walk = enteredHoweverFar(node, blockOf);
        return walk != null && walk.applied() == HowAClosureIsApplied.TO_EVERY_ELEMENT
                ? walk : null;
    }

    /**
     * The same, however far the walk applies its step: for a reader of how a run enters the step,
     * which is with the seed carried into the first application whichever elements are applied
     * to, and that concludes nothing of the elements from it.
     *
     * @param blockOf the block a closure argument stands for, where the call stands
     */
    public static SeededWalk enteredHoweverFar(Core node, Function<Core, Core.Block> blockOf) {
        if (!(Core.withoutStanding(node) instanceof Core.PreservedCall call)) {
            return null;
        }
        Reductions.Reducing walk = Reductions.reducing(call, blockOf);
        return walk == null || walk.element() == null || walk.element().binding() == null
                || walk.accumulator() == null || walk.accumulator().binding() == null
                ? null : new SeededWalk(walk.seed(), walk.container(), walk.step(),
                        walk.accumulator(), walk.element(), walk.applied(),
                        walk.inTheContainersOrder());
    }

    /**
     * This walk read for {@code field} of the record it carries alone, where that field is a walk
     * of its own — or null where it is not.
     *
     * <p>A walk whose seed and step each build the record with every field written out ends with
     * the record whose {@code field} is what that field's own walk ends with, where the step's
     * value for it reads what was carried only as that field. Then the other fields are no part of
     * it, by induction over the walk: what the field comes to after an element is the field's step
     * on what it came to before, and nothing else carried. So the field's walk is this one with the
     * seed the field's seed and the step the field's value in the step, what was carried read
     * there as the field. A field whose step reads another field of what was carried, or the
     * record whole, is no walk of its own, and is not read as one.
     */
    public SeededWalk ofTheField(String field) {
        if (!(Core.withoutStanding(seed) instanceof Core.Construct seeded)
                || !(Core.withoutStanding(step.body()) instanceof Core.Construct stepped)
                || !seeded.typeName().equals(stepped.typeName())) {
            return null;
        }
        Core seedValue = valueGiven(seeded, field);
        Core stepValue = valueGiven(stepped, field);
        if (seedValue == null || stepValue == null) {
            return null;
        }
        BindingId carried = accumulator.binding();
        Core.Read itself = new Core.Read(accumulator.name(), carried, stepValue.type(),
                stepValue.pos());
        Core body = theFieldAsCarried(stepValue, carried, field, itself);
        if (body == null) {
            return null;
        }
        int at = step.params().indexOf(accumulator);
        if (at < 0) {
            return null;
        }
        List<Type> types = new ArrayList<>(step.paramTypes());
        types.set(at, stepValue.type());
        return new SeededWalk(seedValue, container,
                new Core.Block(step.params(), types, body, step.pos()), accumulator, element,
                applied, inTheContainersOrder);
    }

    /** What {@code built} gives {@code field}, or null where it gives it nothing. */
    private static Core valueGiven(Core.Construct built, String field) {
        for (Core.FieldValue each : built.values()) {
            if (each.field().equals(field)) {
                return each.value();
            }
        }
        return null;
    }

    /**
     * {@code e} with {@code field} of what was carried read as {@code itself}; null where what
     * was carried is read any other way, which no walk of the field alone reads.
     */
    private static Core theFieldAsCarried(Core e, BindingId carried, String field,
                                          Core.Read itself) {
        Core node = Core.withoutStanding(e);
        Core.FieldAccess access = switch (node) {
            case Core.FieldAccess one -> one;
            case Core.FieldProjection projection -> projection.lastAccess();
            default -> null;
        };
        if (access != null && Core.withoutStanding(access.target()) instanceof Core.Read name
                && carried.equals(name.binding())) {
            return access.field().equals(field) ? itself : null;
        }
        if (node instanceof Core.Read name && carried.equals(name.binding())) {
            return null;
        }
        boolean[] lost = {false};
        Core out = Core.mapAll(node, child -> {
            Core done = theFieldAsCarried(child, carried, field, itself);
            if (done == null) {
                lost[0] = true;
                return child;
            }
            return done;
        }, name -> name);
        return lost[0] ? null : out;
    }

    /**
     * The end the step keeps of the answer so far and one value it reads of the element alone.
     *
     * @param extreme which end of the two the step answers
     * @param value   the other of the two, which reads nothing of the answer so far, where it is
     *                read: past every name it was given
     * @param <E>     what a reader reads a name in
     */
    public record AnEndKept<E>(Extreme extreme, ValueStanding.ReadThrough<E> value) {}

    /**
     * The end this walk's step keeps, where the step answers the answer so far or one value of the
     * element by how the two stand, and always the same end of them ({@link Extreme#keptBy}) — or
     * null where it answers anything else.
     *
     * <p>Such a step answers the greater or the lesser of what it was carried and that value, so by
     * induction over the walk what the walk ends with is that end of the seed and the value on
     * every element the step was applied to, which for a walk made by {@link #of} is every element
     * of the container. {@code if l.discount > w then l.discount else w}
     * and {@code Int.max(w, l.discount)} keep the greater of {@code w} and {@code l.discount}; a step
     * that adds to what it chose, or chooses by anything but how the two stand, keeps neither.
     *
     * <p>What the step answers is read where the reader reads names
     * ({@link TheSignOfAnOrder.Sides#standing}), and the values its choice reads as they are
     * compared there ({@link Extreme#comparedAs}). So the choice is the same however it is named:
     * {@code { let next = if l.discount > w then l.discount else w  next }},
     * {@code { let d = l.discount  if d > w then d else w }} and the step written out keep one end
     * of {@code w} and {@code l.discount}, and a step comparing {@code l.rate.value} with
     * {@code w.value} and answering {@code l.rate} or {@code w} keeps an end of {@code w} and
     * {@code l.rate}.
     *
     * @param at    where the walk stands
     * @param sides what the reader answers about where it reads
     * @param <E>   what the reader reads a name in
     */
    public <E> AnEndKept<E> endKept(E at, TheSignOfAnOrder.Sides<E> sides) {
        BindingId carried = accumulator.binding();
        ValueStanding.ReadThrough<E> answered = sides.standing(step.body(), at);
        E chosenAt = answered.at();
        List<Choice.ADefinitionCase> cases = Extreme.casesOf(answered.value(), chosenAt, sides);
        ValueStanding.ReadThrough<E> value = null;
        for (Choice.ADefinitionCase each : cases) {
            Core answers = Extreme.answeredBy(each);
            if (answers == null) {
                return null;
            }
            ValueStanding.ReadThrough<E> read = Extreme.comparedAs(answers, chosenAt, sides);
            if (isTheCarried(read.value(), carried)) {
                continue;
            }
            if (value != null && !Core.sameValue(value.value(), read.value())) {
                return null;
            }
            value = read;
        }
        if (value == null || WhatABodyReads.binding(value.value(), carried)) {
            return null;
        }
        Core other = value.value();
        Extreme extreme = Extreme.keptBy(cases,
                e -> isTheCarried(Extreme.comparedAs(e, chosenAt, sides).value(), carried),
                e -> Core.sameValue(Extreme.comparedAs(e, chosenAt, sides).value(), other));
        return extreme == null ? null : new AnEndKept<>(extreme, value);
    }

    private static boolean isTheCarried(Core e, BindingId carried) {
        return Core.withoutStanding(e) instanceof Core.Read read
                && carried.equals(read.binding());
    }
}
