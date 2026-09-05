package souther.compiler.check;

import souther.compiler.core.Core;

/**
 * A clause tree read into one state, the connectives being the same whatever the leaves are read as.
 *
 * <p>What a clause is written out of — a conjunction, a choice, a denial — is the clause's own shape
 * and not a fact about the language it is read in. Written once per language, that shape is the same
 * code as many times as there are languages, and each copy is free to drift from the others.
 *
 * <p><b>And the connectives belong to the clause and not to a component of the state.</b> That is
 * what this is for. A choice between two alternatives is a choice between two <em>readings of the
 * whole value</em>, so the alternative that cannot be taken has to be dropped by asking the whole of
 * what is known about it. Applied inside each language on its own, an alternative was dropped only
 * where the language doing the joining was also the one that could show it impossible — and a choice
 * between a branch no order admits and a branch no set of values admits came out open, each language
 * having found nothing wrong with the branch the other one refused.
 *
 * <p><b>What a clause states is answered upward and what its names mean is handed downward.</b> A
 * reading composes its leaves into one answer, and that answer is a function of the leaves; the
 * environment a leaf is read in is a function of the bindings above it, which is the other
 * direction. Carried only upward, there was nowhere for a binding to be, so a clause under one was
 * a shape every reading had no word for — and since almost every binding this check meets is one a
 * helper's expansion made, a rule stated through a helper was read less than the same rule written
 * out.
 *
 * <p>So {@code E} is handed down and {@code S} comes back up, and a leaf is read at the environment
 * it stands in. What a binding does to that environment is not asked of a reading: the fold finds
 * the boundary and {@link ClauseScope} answers it, which is what keeps a binder's meaning the
 * environment's (ADR-0106) rather than something each of three readings works out again.
 *
 * @param <S> what a reading of a clause comes to
 * @param <E> what the reading carries into a binding — what its leaves are read at
 */
interface ClauseReading<S, E> {

    /** What a clause this reading has no word for leaves, which is everything it had. */
    S nothingSaid();

    /**
     * What one clause of no connective says, stated where {@code positive} and denied where it is
     * not, read at the environment {@code at} it stands in.
     *
     * <p>Reached with the denials already counted, so a reading of a comparison is a reading of the
     * comparison it states rather than of the one that was written. And reached with the bindings
     * above it entered, so a name a helper's expansion introduced denotes what it was given — a
     * reading that answered from the environment the whole clause began in would be reading one
     * value's rule at another value's names.
     */
    S leaf(Core e, boolean positive, E at);

    /** Both readings holding at once. */
    S both(S one, S other);

    /**
     * Either reading holding, at the connective an author wrote it with.
     *
     * <p>The node is here because a reading with something to say about the choice has nowhere else
     * to learn where it stands. What the fold hands up is two readings and a flag; which choice they
     * are the two branches of is known at this call and at no call after it, so a reading that wants
     * it and is not given it here works it out from something else — and the something else is
     * whichever place a walk happened to reach, which is a fact about the walk.
     */
    S either(Core writtenAt, S one, S other);

    /**
     * What {@code e} leaves, stated where {@code positive} and denied where it is not, read from
     * {@code at} with {@code scope} answering for the bindings inside it.
     *
     * <p>A denial is carried to the leaves rather than applied to what a branch came to. What a
     * state says is a fact per position, and the denial of that is not one — the values a
     * conjunction rules out are a choice between the positions it named, which no map of positions
     * holds. Carried down, every denial meets a leaf, where it is one.
     */
    default S read(Core e, boolean positive, E at, ClauseScope<E> scope) {
        return read(e, positive, at, scope, null);
    }

    /**
     * The same, telling {@code per} what each part of the clause came to as it is read.
     *
     * <p>Keyed by the part as the tree holds it, so a reader that walks the same clause afterwards
     * finds what this reading made of the very node it is looking at. Asked again instead, that
     * reader is a second reading of the part, and two readings of one conjunct agree only for as
     * long as nobody changes one of them.
     */
    default S read(Core e, boolean positive, E at, ClauseScope<E> scope,
                   java.util.function.BiConsumer<Core, S> per) {
        S out = from(e, over(ClauseExpr.of(e, positive), at, scope, per));
        if (per != null) {
            per.accept(e, out);
        }
        return out;
    }

    /**
     * The same reading over the shape a clause has, which is read out of the tree once
     * ({@link ClauseExpr}).
     *
     * <p>Here rather than over {@link Core}, so that what counts as a connective is settled in one
     * place and every reading agrees about it by having been given the answer. Two readings that
     * each recognised {@code &&} for themselves agreed until one of them learned something.
     */
    private S over(ClauseExpr shape, E at, ClauseScope<E> scope,
                   java.util.function.BiConsumer<Core, S> per) {
        S out = switch (shape) {
            case ClauseExpr.Leaf it -> leaf(it.of(), it.positive(), at);
            case ClauseExpr.Joined it -> switch (it.how()) {
                case BOTH -> both(over(it.left(), at, scope, per), over(it.right(), at, scope, per));
                case EITHER -> either(it.of(), over(it.left(), at, scope, per),
                        over(it.right(), at, scope, per));
            };
            // The one place the environment changes, and it changes for what is under the binding
            // alone. What the binding means is not worked out here and not by the reading either.
            case ClauseExpr.Scoped it ->
                    over(it.body(), scope.inside(it.binding(), at), scope, per);
        };
        // Every node that was written as this shape, so a reader asking about the node it is
        // holding finds what this made of it — the denial as well as what is under it, since the
        // two are one shape, and the binding as well as the clause under it, since a binding states
        // what the clause under it states.
        for (Core each : shape.spelled()) {
            out = from(each, out);
            if (per != null) {
                per.accept(each, out);
            }
        }
        return out;
    }

    /**
     * The same reading, remembering that it is what {@code e} came to.
     *
     * <p>For a reading that has to answer about the parts of a clause afterwards. Kept in what the
     * reading carries rather than handed to somebody who keeps it: a part of a branch that turns
     * out dead is answered differently from the same part in a branch that stands, and everything
     * that decides which of those it was happens above here. Kept outside, the part would be read
     * again against a tree the decision had not reached.
     */
    default S from(Core e, S out) {
        return out;
    }
}
