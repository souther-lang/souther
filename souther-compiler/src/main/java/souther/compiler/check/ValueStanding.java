package souther.compiler.check;

import souther.compiler.core.ConstructionProjection;
import souther.compiler.core.Core;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Predicate;

/**
 * What an occurrence stands as, once every step with one successor has been taken: a name the
 * environment says denotes one value, a binding's body, an elimination standing against the
 * introduction that wrote it, and a value the environment takes as another.
 *
 * <p><b>One account of how far a value is followed, for every environment.</b> Which names denote
 * which values is the environment's answer ({@link Names}); how far those answers reach is this
 * walk's, and it is the same walk whatever is asked of the value it ends at. A reader that followed
 * names for itself would reach the value behind a name for the values it happened to follow — a
 * number, say — and stop at the name in front of a case or a string.
 *
 * <p><b>Nothing here chooses.</b> A name the environment names several values for is followed into
 * all of them, and only where the environment answers with a plurality at all
 * ({@link Names#alternativesOf}). Where it answers none, every step has one successor and the walk
 * ends at one value. A choice is neither: the environment gives it no plurality, and where it says
 * which arm a reading is on ({@link Names#taken}) the choice is that arm's answer.
 *
 * <p><b>Closed under its own eliminations.</b> A projection resolves through whatever the target
 * resolves to, so a construction inside a construction is reached the same way a construction behind
 * a name is. What a construction gives a field is {@link ConstructionProjection}'s answer and not a
 * rule here.
 *
 * <p><b>A normal form and never a failure.</b> What comes back is where the steps run out — the
 * occurrence itself where none applies. Reaching a {@code Core.If} is such a result and not an
 * absence: what stands there is known perfectly well, and it is a choice rather than a value. So a
 * caller reads what it was handed and never treats getting its own expression back as an answer
 * about this walk.
 *
 * <p><b>The authority is the environment's and none is added here.</b> A name is followed only
 * where {@link Names#readThrough} licenses that occurrence, and a binding is entered only through
 * {@link Names#inside}. What is derived is how far those answers reach, which is not the same kind
 * of thing as the answers — so this is not the place to ask what an environment happens to hold.
 */
public final class ValueStanding {

    private ValueStanding() {}

    /**
     * What a name was given, and what to read it in.
     *
     * <p>The environment comes with the value because the two belong together: a value stands for
     * the name in the environment the binding was made in, which is not always the one the name was
     * read in. Where a caller cannot tell the two apart it hands back the environment it was given
     * and says why — carried in the type either way, so the day they come apart there is one place
     * that answers for it.
     */
    public record ReadThrough<E>(Core value, E at) {}

    /**
     * What a walk asks the environment a value is read in, and nothing else.
     *
     * @param <E> the environment
     * @param <N> what answers for it, which is what the parts of a value reached are read with
     */
    public interface Names<E, N extends Names<E, N>> {

        /**
         * The value {@code read}'s name denotes, where the name and that value are one value — or
         * null where the name stands for something of its own and reading through it would say of
         * one value what was written about another.
         *
         * <p>Answered from the environment, which is what knows. A name is a place the caller's
         * seeding wrote about, or a position of a behavior's input, or an element an operation
         * handed out, or the expression it was given, and which of those it is decides whether
         * anything may stand where it stands. What is answered is the expression alone: what it
         * comes to is read by whoever asked, once, so no environment keeps a second account of it.
         */
        ReadThrough<E> readThrough(Core.Read read, E at);

        /**
         * Every value {@code read}'s name can stand for, where the environment has all of them — or
         * null where it has not, or gives no plurality.
         *
         * <p>Beside {@link #readThrough} and answering the other half of one question. That one says
         * the name and one value are one value; this says the name is one of these and names them
         * all. A name has at most one of the two answers, and which it is is the environment's to
         * say: a reader that took a plurality for a denotation would state of one value what the
         * model says of several, and one that took a denotation for a plurality would be asking what
         * a single value agrees with.
         *
         * <p><b>Exhaustive, or null.</b> What a reader does with the answer is keep what every
         * member comes to, and a member left out makes that a statement about a value the name can
         * take with nothing said. So an environment that can write out some of them answers none.
         */
        List<ReadThrough<E>> alternativesOf(Core.Read read, E at);

        /** What {@code li}'s body is read in. The one place a binding is entered, so that what a
         *  name means is settled once and no reader interprets a binder for itself. */
        E inside(Core.LetIn li, E at);

        /**
         * The value the environment takes {@code node} as — the answer of the arm a reading is on,
         * where it is a choice; the body a reading entered, where it is a call — or null where it
         * takes it as nothing else.
         *
         * <p>The environment's answer and not a rule of the walk, for the reason a name's is: the
         * walk chooses nothing and calls nothing. A caller reading something once for each arm of a
         * choice inside it, or reading a call through what it calls, hands the walk an environment
         * that says so, and the node is then one value, as a name the environment reads through is.
         */
        default ReadThrough<E> taken(Core node, E at) {
            return null;
        }

        /**
         * What tells what {@code read}'s name stands for in {@code at} apart from what it stands for
         * elsewhere — what a reader holding an answer for each name keys it on. {@code at} itself
         * unless the environment can say less: two environments in which the name stands for the
         * one thing, read the one way, give it one answer, and a reader keyed on each environment
         * would work that answer out again in every one of them.
         */
        default Object standingOf(Core.Read read, E at) {
            return at;
        }

        /**
         * That a name or a field was read at {@code place}, in {@code at}, and is about to be read
         * through.
         *
         * <p>Told by the walk that follows names and takes fields off what was written, which is the
         * one place either is done, and told before what it stands for is known: where the name is
         * one of several values, or the field of a value written down, the place read is what says
         * whose it was. For an environment that is asked what a value was made of; nothing
         * otherwise.
         */
        default void noticed(Core place, E at) {
        }

        /**
         * These answers with no plurality in them, which is what the values a name stands for are
         * read with.
         *
         * <p>One plurality per question. Reading a member that is itself several means asking of
         * every pairing, and a value written down a chain of them is two to the power of its depth.
         * Said as what the members are read with rather than as a count or a depth, so the boundary
         * holds over the parts of a member as well as over the member.
         */
        N oneAtATime();
    }

    /**
     * An occurrence followed as far as one value can be, what to read it in, and what to read it
     * with.
     *
     * <p>The environment travels with the value because a value stands for a name in the
     * environment the binding was made in, which is not always the one the name was read in. The
     * answers travel with it for the same kind of reason: a value reached by taking one of several is
     * read without a plurality of its own ({@link Names#oneAtATime}), and left behind, that
     * restriction would be gone by the time its parts were read.
     */
    public record Standing<E, N extends Names<E, N>>(Core value, E at, N names) {

        /**
         * {@code part}, a part of this value as it was written, followed where this value was
         * written — or {@code part} itself where it stands for several values.
         *
         * <p>Where a reader takes a value apart, what it finds inside is written in the environment
         * the value was, and it is followed there before it is read. A part handed on as written
         * would put a name back in front of the reader that the value it came out of had already
         * been followed past.
         */
        public Standing<E, N> part(Core part) {
            return one(part, at, names);
        }
    }

    /**
     * {@code e} read in {@code at}, followed as far as one value goes.
     *
     * <p>Walked with no plurality in the answers ({@link Names#oneAtATime}), so a name that is one
     * of several values stands as the name: it is not one value, however many values it is one of —
     * one included. Which a name is, is the environment's answer ({@link Named}), and a walk that
     * followed it into its values and counted them afterwards would be deciding it again by how
     * many there happened to be.
     */
    public static <E, N extends Names<E, N>> Standing<E, N> one(Core e, E at, N names) {
        List<Standing<E, N>> reached = of(e, at, names.oneAtATime());
        if (reached.size() != 1) {
            throw new IllegalStateException("a walk with no plurality in it reached "
                    + reached.size() + " values from " + e.pos());
        }
        return reached.getFirst();
    }

    /** {@code e} read in {@code at}, followed as far as the steps go: one value where the
     *  environment has no plurality to give, and every value it stands for where it has. */
    public static <E, N extends Names<E, N>> List<Standing<E, N>> of(Core e, E at, N names) {
        return of(e, at, names, new BindingWalk<Void>());
    }

    /**
     * Where one name leads: the one value it denotes, or every value it is one of.
     *
     * <p>Two answers and not a list whose length says which. A name that is one value is read as
     * that value; a name that is one of several is read as what they agree on. Told apart by how
     * many there happen to be, a plurality of one would be taken for a denotation.
     */
    public sealed interface Named<E, N extends Names<E, N>> {

        /** The name and this value are one value. */
        record One<E, N extends Names<E, N>>(Standing<E, N> value) implements Named<E, N> {}

        /** The name is one of these, every one of them, each read without a plurality of its own
         *  ({@link Names#oneAtATime}). */
        record OneOf<E, N extends Names<E, N>>(List<Standing<E, N>> members)
                implements Named<E, N> {}
    }

    /**
     * Where the name {@code r} leads in {@code at}, or null where it leads nowhere: a name standing
     * for something of its own, or one the environment says is itself.
     *
     * <p>The one place a name is followed. Whether the walk below goes past a name, and whether a
     * reader composing what a name comes to does, is this answer; a reader asking the environment
     * for itself is a second account of which names may be followed.
     */
    public static <E, N extends Names<E, N>> Named<E, N> named(Core.Read r, E at, N names) {
        names.noticed(r, at);
        ReadThrough<E> through = names.readThrough(r, at);
        if (through != null) {
            return through.value() == r ? null
                    : new Named.One<>(new Standing<>(through.value(), through.at(), names));
        }
        List<ReadThrough<E>> alternatives = names.alternativesOf(r, at);
        return alternatives == null || alternatives.isEmpty() ? null
                : new Named.OneOf<>(membersOf(alternatives, names));
    }

    /** What the environment takes {@code node} as, followed no further, or null where it takes it
     *  as nothing else ({@link Names#taken}). */
    public static <E, N extends Names<E, N>> Standing<E, N> taken(Core node, E at, N names) {
        ReadThrough<E> taken = names.taken(node, at);
        return taken == null ? null : new Standing<>(taken.value(), taken.at(), names);
    }

    /** The same, inside a walk already following names, which says where following one stops. */
    static <E, N extends Names<E, N>> List<Standing<E, N>> of(Core asPlaced, E at, N names,
                                                              BindingWalk<?> following) {
        // What a value is does not turn on the type it stands as at its position.
        Core e = Core.withoutStanding(asPlaced);
        return switch (e) {
            case Core.Read r -> {
                Named<E, N> led = named(r, at, names);
                if (led == null || !following.enter(r.binding())) {
                    yield List.of(new Standing<>(e, at, names));
                }
                List<Standing<E, N>> reached = switch (led) {
                    case Named.One<E, N>(Standing<E, N> one) ->
                            of(one.value(), one.at(), one.names(), following);
                    case Named.OneOf<E, N>(List<Standing<E, N>> members) -> {
                        List<Standing<E, N>> each = new ArrayList<>();
                        for (Standing<E, N> one : members) {
                            each.addAll(of(one.value(), one.at(), one.names(), following));
                        }
                        yield each;
                    }
                };
                following.leave(r.binding());
                yield reached;
            }
            case Core.LetIn li -> of(li.body(), names.inside(li, at), names, following);
            case Core.Widen w -> of(w.value(), at, names, following);
            // The elimination below a name at a time, along the names rather than down the stack.
            // A name with nothing written to stand against leaves the whole projection standing,
            // as it leaves every access above it standing when they are written out.
            case Core.FieldProjection p -> {
                names.noticed(p, at);
                List<Standing<E, N>> reached = of(p.base(), at, names, following);
                // Asked before the names are written out: a base standing at no construction has
                // nothing written against its first name, and the names are as many as the chain
                // is deep.
                if (!allConstructions(reached)) {
                    yield List.of(new Standing<>(e, at, names));
                }
                for (Core.FieldProjection.Step step : p.steps().inOrder()) {
                    List<Standing<E, N>> written = given(reached, step.field());
                    if (written == null) {
                        yield List.of(new Standing<>(e, at, names));
                    }
                    reached = new ArrayList<>();
                    for (Standing<E, N> one : written) {
                        reached.addAll(of(one.value(), one.at(), one.names(), following));
                    }
                }
                yield reached;
            }
            case Core.FieldAccess _, Core.TupleGet _ -> {
                List<Standing<E, N>> written = eliminated(e, at, names, following);
                if (written == null) {
                    yield List.of(new Standing<>(e, at, names));
                }
                if (written.size() == 1) {
                    Standing<E, N> one = written.getFirst();
                    yield of(one.value(), one.at(), one.names(), following);
                }
                List<Standing<E, N>> each = new ArrayList<>();
                for (Standing<E, N> one : written) {
                    each.addAll(of(one.value(), one.at(), one.names(), following));
                }
                yield each;
            }
            default -> {
                Standing<E, N> taken = taken(e, at, names);
                yield taken == null ? List.of(new Standing<>(e, at, names))
                        : of(taken.value(), taken.at(), names, following);
            }
        };
    }

    /**
     * What this elimination stands against, or null where nothing written stands against it.
     *
     * <p><b>One question with one answer, asked by the two readings that have it.</b> Following an
     * occurrence needs to know what an elimination came to so it can go on, and reading a form
     * needs to know it so it can compose — and where it comes to nothing, the second has another
     * proof to try. Written out at each of them, one copy would come to read a shape the other did
     * not, and which shapes a rule about eliminations covers would depend on which reader met it.
     *
     * <p><b>Null is the rule not applying, and never the kind of node.</b> A construction that does
     * not give the field asked for has nothing written to stand against, exactly as an expression
     * that is no construction has not — so a caller asking whether the structural reading produced
     * a successor is asking one thing.
     *
     * <p><b>Taken of every value the target can stand at, or of none of them.</b> A projection out
     * of a name that stands for several is that projection out of each of them, and one member with
     * nothing written to stand against takes the answer away for all of them: what a caller is going
     * to state is what the members agree on, and a member this could not eliminate is one it has
     * nothing to compare.
     */
    static <E, N extends Names<E, N>> List<Standing<E, N>> eliminated(
            Core e, E at, N names, BindingWalk<?> following) {
        return switch (Core.withoutStanding(e)) {
            case Core.FieldAccess fa -> {
                names.noticed(fa, at);
                yield given(of(fa.target(), at, names, following), fa.field());
            }
            // Its last name against what the names before it reach.
            case Core.FieldProjection p -> {
                names.noticed(p, at);
                yield given(of(p.target(), at, names, following), p.steps().last().field());
            }
            case Core.TupleGet get -> {
                List<Standing<E, N>> out = new ArrayList<>();
                for (Standing<E, N> tuple : of(get.tuple(), at, names, following)) {
                    if (!(Core.withoutStanding(tuple.value()) instanceof Core.Tuple written)
                            || get.index() < 0
                            || get.index() >= written.elements().size()) {
                        yield null;
                    }
                    out.add(new Standing<>(written.elements().get(get.index()), tuple.at(),
                            tuple.names()));
                }
                yield out;
            }
            default -> null;
        };
    }

    /**
     * The one construction {@code target} stands at, with where it stands, or null where it stands
     * at none or at several.
     *
     * <p>Asked of the target of an elimination that produced a successor, for a reader that reads
     * what the elimination takes off a construction as that construction: the check made when it
     * is made is then its own to tell of. Several constructions are several checks of which one is
     * made, and no one of them is told as the check of the value.
     */
    static <E, N extends Names<E, N>> Standing<E, N> theOneConstructionAt(
            Core target, E at, N names, BindingWalk<?> following) {
        List<Standing<E, N>> reached = of(target, at, names, following);
        return reached.size() == 1
                && Core.withoutStanding(reached.getFirst().value()) instanceof Core.Construct
                ? reached.getFirst() : null;
    }

    /**
     * Whether making the construction a field access is read off, and working out its parts other
     * than the field it reads, end no run: both are done all the same, and one that ends a run is
     * an operation the reading of the field does not tell of. The construction itself ends one
     * where its type has an invariant, which is checked when it is made; a part ends none only
     * when it is written out under the construction and names nothing, since what a name stands
     * for was worked out where it was bound, out of this reading's sight. False where nothing
     * written stands against the access, which has no construction to ask.
     */
    static <E, N extends Names<E, N>> boolean theConstructionAndItsRestEndNone(
            Core.FieldAccess fa, E at, N names, BindingWalk<?> following,
            Predicate<Core.Construct> makingEndsNone) {
        for (Standing<E, N> target : of(fa.target(), at, names, following)) {
            if (!(Core.withoutStanding(target.value()) instanceof Core.Construct nd)
                    || !makingEndsNone.test(nd)) {
                return false;
            }
            Core read = ConstructionProjection.given(nd, fa.field());
            for (var part : nd.values()) {
                if (part.value() != read
                        && !WhatARunMayEndFor.endsNoneAndReadsNoNameBeneath(part.value())) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * What each of {@code targets} gives {@code field}, or null where one of them is no construction
     * giving it — one field taken off what a projection's target stands at.
     */
    private static <E, N extends Names<E, N>> List<Standing<E, N>> given(
            List<Standing<E, N>> targets, String field) {
        if (!allConstructions(targets)) {
            return null;
        }
        List<Standing<E, N>> out = new ArrayList<>();
        for (Standing<E, N> target : targets) {
            Core.Construct nd = (Core.Construct) Core.withoutStanding(target.value());
            Core written = ConstructionProjection.given(nd, field);
            if (written == null) {
                return null;
            }
            // What a member gives a field is read with what the member is read with, which is how
            // one plurality stays one over the parts of it.
            out.add(new Standing<>(written, target.at(), target.names()));
        }
        return out;
    }

    /** Whether every one of {@code targets} stands at a construction, which is all a field can be
     *  written against: one that does not has nothing written for any name taken off it. */
    private static <E, N extends Names<E, N>> boolean allConstructions(
            List<Standing<E, N>> targets) {
        for (Standing<E, N> target : targets) {
            if (!(Core.withoutStanding(target.value()) instanceof Core.Construct)) {
                return false;
            }
        }
        return true;
    }

    /**
     * The values a name stands for, each to be read without a plurality of its own.
     *
     * <p><b>One plurality per question, said here and nowhere else.</b> What a reader answers about
     * a position several values stand at is what all of them support, and reading a member that is
     * itself several means asking that of every pairing: two members whose members have two each is
     * four readings, and a value written down a chain of them is two to the power of its depth. That
     * is a capability with a cost, and it is not the one asked for: a container written out in the
     * source is what a model states its values in.
     */
    private static <E, N extends Names<E, N>> List<Standing<E, N>> membersOf(
            List<ReadThrough<E>> alternatives, N names) {
        List<Standing<E, N>> out = new ArrayList<>();
        N once = names.oneAtATime();
        alternatives.forEach(each -> out.add(new Standing<>(each.value(), each.at(), once)));
        return out;
    }
}
