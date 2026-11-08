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
     * One part of a value: a field of a record, or a component of a tuple.
     *
     * <p>The two are one question to a reader of what a walk carries. A walk carrying a record and
     * one carrying a tuple carry several values side by side, and which of them a reader takes is
     * all that differs between {@code state.score} and {@code let (score, _) = state}.
     */
    public sealed interface Part {

        /** The field named {@code name} of a record. */
        record Field(String name) implements Part {}

        /** The component at {@code index} of a tuple. */
        record Component(int index) implements Part {}

        /**
         * The value {@code node} takes a part of and which part, where it takes one — or null
         * where it is anything else.
         */
        static Taken taken(Core node) {
            return switch (Core.withoutStanding(node)) {
                case Core.FieldAccess one -> new Taken(one.target(), new Field(one.field()),
                        one.type());
                case Core.FieldProjection projection -> new Taken(
                        projection.lastAccess().target(),
                        new Field(projection.lastAccess().field()), projection.type());
                case Core.TupleGet get -> new Taken(get.tuple(), new Component(get.index()),
                        get.type());
                default -> null;
            };
        }

        /**
         * What {@code built} gives this part where it is written out — a record built with the
         * field, or a tuple written with the component — or null where it is anything else.
         */
        default Core givenBy(Core built) {
            return switch (this) {
                case Field(String name) when Core.withoutStanding(built)
                        instanceof Core.Construct construct -> {
                    for (Core.FieldValue each : construct.values()) {
                        if (each.field().equals(name)) {
                            yield each.value();
                        }
                    }
                    yield null;
                }
                case Component(int index) when Core.withoutStanding(built)
                        instanceof Core.Tuple tuple
                        && index >= 0 && index < tuple.elements().size() ->
                        tuple.elements().get(index);
                case Field _, Component _ -> null;
            };
        }
    }

    /**
     * The value {@code whole} that {@code part} is taken of.
     *
     * @param whole what the part is taken of
     * @param part  which part of it
     * @param type  the type the part is read at, which a walk of it alone carries it as: a seed
     *              written as an empty list says less of it
     */
    public record Taken(Core whole, Part part, Type type) {}

    /**
     * This walk read for the part {@code part} takes of what it carries alone, where that part is
     * a walk of its own — or null where it is not.
     *
     * <p>A walk whose seed is written out with the part, and whose step answers, on every way
     * through it, the value written out with the part or what it was carried, ends with the value
     * whose {@code part} is what that part's own walk ends with, where the step reads what was
     * carried only as that part. Then the other parts are no part of it, by induction over the
     * walk: what the part comes to after an element is the part's step on what it came to before,
     * and nothing else carried. So the part's walk is this one with the seed the part of the seed
     * and the step the part of what the step answers, what was carried read there as the part.
     *
     * <p>The step is read through what it names and chooses on the way to what it answers. A name
     * given a value read off what was carried stands for that value where it is read, so
     * {@code let (n, ys) = acc} reads {@code n} only where the part does, and a name the part
     * never reads is read nowhere. A choice answers the part of what each arm answers. A part
     * whose step reads another part of what was carried, or what was carried whole, is no walk of
     * its own, and is not read as one.
     */
    public SeededWalk ofThePart(Taken part) {
        OfThePart alone = ofThePart(seed, step, accumulator, part);
        return alone == null ? null : new SeededWalk(alone.seed(), container, alone.step(),
                accumulator, element, applied, inTheContainersOrder);
    }

    /**
     * What a walk of {@code part} alone starts from and repeats.
     *
     * @param seed the seed of the part alone
     * @param step the step of the part alone, handed the part as what it carries
     */
    public record OfThePart(Core seed, Core.Block step) {}

    /**
     * The walk from {@code seed} repeating {@code step}, which is handed what it carries as
     * {@code accumulator}, read for the part {@code taken} takes of what it carries alone, as
     * {@link #ofThePart(Taken)} says — or null where that part is no walk of its own.
     *
     * <p>Of the seed, the step and the name alone, so a reader that has a walk of its own making
     * reads a part of it as the same walk.
     */
    public static OfThePart ofThePart(Core seed, Core.Block step, Core.Binder accumulator,
                                      Taken taken) {
        Part part = taken.part();
        Core seedValue = part.givenBy(seed);
        if (seedValue == null || accumulator == null || accumulator.binding() == null) {
            return null;
        }
        int at = step.params().indexOf(accumulator);
        if (at < 0) {
            return null;
        }
        Type partType = taken.type();
        BindingId carried = accumulator.binding();
        Core.Read itself = new Core.Read(accumulator.name(), accumulator.binding(), partType,
                seedValue.pos());
        Core answered = partAnswered(step.body(), part, carried, itself);
        Core body = answered == null ? null : thePartAsCarried(answered, carried, part, itself);
        if (body == null) {
            return null;
        }
        List<Type> types = new ArrayList<>(step.paramTypes());
        types.set(at, partType);
        return new OfThePart(seedValue, new Core.Block(step.params(), types, body, step.pos()));
    }

    /**
     * The part {@code part} of what {@code e} answers, on every way through it: the part written
     * out where it builds the value, {@code itself} where it answers what was carried, and the
     * same of each arm of a choice and of what a {@code let} answers. Null where some way answers
     * anything else.
     */
    private static Core partAnswered(Core e, Part part, BindingId carried, Core.Read itself) {
        Core node = Core.withoutStanding(e);
        if (isTheCarried(node, carried)) {
            return itself;
        }
        Core given = part.givenBy(node);
        if (given != null) {
            return given;
        }
        return switch (node) {
            case Core.LetIn let -> {
                Core body = partAnswered(let.body(), part, carried, itself);
                if (body == null) {
                    yield null;
                }
                yield new Core.LetIn(let.binder(), let.bindType(), let.value(), body,
                        body.type(), let.pos());
            }
            case Core.If fork -> {
                Core then = partAnswered(fork.then(), part, carried, itself);
                Core els = then == null ? null : partAnswered(fork.els(), part, carried, itself);
                yield els == null ? null
                        : new Core.If(fork.cond(), then, els, fork.place(), then.type(),
                                fork.pos());
            }
            case Core.Match match -> {
                List<Core.Case> arms = new ArrayList<>();
                for (Core.Case arm : match.cases()) {
                    Core body = partAnswered(arm.body(), part, carried, itself);
                    if (body == null) {
                        yield null;
                    }
                    arms.add(new Core.Case(arm.pattern(), arm.binding(), body, arm.pos()));
                }
                yield arms.isEmpty() ? null : new Core.Match(match.scrutinee(), arms,
                        match.place(), arms.getFirst().body().type(), match.pos());
            }
            default -> null;
        };
    }

    /**
     * {@code e} with {@code part} of what was carried read as {@code itself}; null where what was
     * carried is read any other way, which no walk of the part alone reads.
     */
    private static Core thePartAsCarried(Core e, BindingId carried, Part part,
                                         Core.Read itself) {
        Core node = Core.withoutStanding(e);
        if (node == itself) {
            return itself;
        }
        Taken taken = Part.taken(node);
        if (taken != null && isTheCarried(taken.whole(), carried)) {
            return taken.part().equals(part) ? itself : null;
        }
        if (isTheCarried(node, carried)) {
            return null;
        }
        // A name given a value read off what was carried stands for that value, put where it is
        // read: the name is the walk's own, and a reader following it would find the whole that
        // was carried. A pattern's name for the whole, {@code let (n, ys) = acc}, among them.
        if (node instanceof Core.LetIn let && WhatABodyReads.binding(let.value(), carried)) {
            Core body = inlined(let.body(), let.binder().binding(), let.value());
            return body == null ? null : thePartAsCarried(body, carried, part, itself);
        }
        boolean[] lost = {false};
        Core out = Core.mapAll(node, child -> {
            Core done = thePartAsCarried(child, carried, part, itself);
            if (done == null) {
                lost[0] = true;
                return child;
            }
            return done;
        }, name -> {
            lost[0] |= carried.equals(name.binding());
            return name;
        });
        return lost[0] ? null : out;
    }

    /**
     * {@code e} with {@code value} where it reads {@code name} — or null where a slot that takes
     * only a name reads it, which no value can stand in.
     */
    private static Core inlined(Core e, BindingId name, Core value) {
        Core node = Core.withoutStanding(e);
        if (node instanceof Core.Read read && read.binding() != null
                && read.binding().equals(name)) {
            return value;
        }
        boolean[] lost = {false};
        Core out = Core.mapAll(node, child -> {
            Core done = inlined(child, name, value);
            if (done == null) {
                lost[0] = true;
                return child;
            }
            return done;
        }, slot -> {
            lost[0] |= slot.binding() != null && slot.binding().equals(name);
            return slot;
        });
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
