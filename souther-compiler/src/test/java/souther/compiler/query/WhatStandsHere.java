package souther.compiler.query;


/**
 * What a walk found at one place, said as one of the things it can be.
 *
 * <p><b>One reading of the order, for every walk.</b> Whether something can be compared as a value
 * is a question asked in a sequence — a container is read for what it holds only once it has said
 * that comparing it compares them, a sum is taken apart only once something closes it — and the
 * sequence is what carries the meaning. Written as a chain of tests inside each walk, the sequence
 * is a fact about the order somebody happened to write the branches in: one walk asked what a
 * container holds before asking whether the container says anything, and everything under it came
 * back clean.
 *
 * <p>So a walk answers about the thing in front of it and nothing else, and the order those answers
 * are read in is here. What is left to a walk is what a thing <em>is</em> — the same question asked
 * of an object a store holds and of a type a question declares — and the two cannot come apart over
 * the sequence, because there is one.
 *
 * @param <N> what a walk holds at a place: an object, or a type with its letters bound
 * @param <P> the way down to it
 */
sealed interface WhatStandsHere<N, P> {

    /** One way down and what is at the end of it. */
    record Under<N, P>(P where, N node) {}

    /** Something the language says the meaning of, which no walk has anything to add about. */
    record ALanguageValue<N, P>() implements WhatStandsHere<N, P> {}

    /** An array, which says which object it is however its elements compare. */
    record AnArray<N, P>() implements WhatStandsHere<N, P> {}

    /** Something whose equality is its members', read for the members. */
    record AContainerOf<N, P>(Covered<Under<N, P>> held) implements WhatStandsHere<N, P> {}

    /** A sum, read for every arm nothing else can be. */
    record ASumOf<N, P>(Covered<Under<N, P>> arms) implements WhatStandsHere<N, P> {}

    /**
     * A sum that is also a thing of its own, read for both.
     *
     * <p>A closed family whose head can be built has arms and members that are each what may stand
     * here. Read for the arms alone, what the head itself holds would go unasked.
     */
    record AClosedFamily<N, P>(Covered<Under<N, P>> members, Covered<Under<N, P>> arms)
            implements WhatStandsHere<N, P> {}

    /** Something that says what it is and nothing else can be, read for what it holds. */
    record AClosedValue<N, P>(Covered<Under<N, P>> members) implements WhatStandsHere<N, P> {}

    /** Something that says only which object it is. */
    record SaysNothingOfItself<N, P>() implements WhatStandsHere<N, P> {}

    /** Something anything may extend or implement, so what stands here is settled by whatever was
     *  put there rather than by what was declared. */
    record NothingClosesIt<N, P>() implements WhatStandsHere<N, P> {}

    /** A letter or a wildcard nothing here binds. */
    record NotBound<N, P>() implements WhatStandsHere<N, P> {}

    /**
     * What one walk answers about one thing, and never about the order to ask in.
     *
     * <p>Each of these is a fact about what is in front of the walk. A walk that answered them by
     * asking them in an order of its own would be the sequence living in two places again.
     *
     * <p><b>Every way down comes back saying whether it is all of them.</b> Reading what a thing
     * holds may not reach all of it, and where it did not is part of the answer. Handed back as a
     * list, that is something a walk has to be told some other way and whoever takes the list has
     * to remember to go and ask — which is how a thing half of which would not open came back
     * covered, was put away as looked at, and left the next path to hold it with nothing to see.
     */
    interface Facts<N, P> {

        /** Whether anything at all is known to stand here. */
        boolean bound(N node);

        /** What is here, by class, where anything is. */
        Class<?> classOf(N node);

        /** Whether this is something whose equality is what it holds — a list, a set, a map, what
         *  an absence may be hiding — written so that what it holds is known. */
        boolean aContainer(N node);

        /** What it holds, asked only of a container. */
        Covered<Under<N, P>> held(N node, P where);

        /** Whether what may stand here is written down: a sum, whichever way it is spelled. */
        boolean closedFamily(N node);

        /** The arms of that family. */
        Covered<Under<N, P>> arms(N node, P where);

        /** Whether anything of this may itself be built, rather than only the arms under it. */
        boolean itselfStands(N node);

        /** Whether nothing else can stand where this is declared. */
        boolean closesWhatStandsHere(N node);

        /** What it holds beside its own identity. */
        Covered<Under<N, P>> members(N node, P where);
    }

    /**
     * What stands at {@code node}, read in the one order.
     *
     * <p>Read down the list, and the reason each comes where it does:
     *
     * <ul>
     *   <li>nothing is known to stand here, so nothing further is worth asking;
     *   <li>the language says what it is;
     *   <li>an array, which says which object it is whatever it holds;
     *   <li>a container, which stands for what it holds only if comparing it compares them — asked
     *       before what it holds, which is the whole of what one walk got wrong;
     *   <li>a type whose inhabitants are not it — an interface, or something abstract. Closed, it is
     *       its arms; open, nothing says what stands here, and no equality written anywhere would
     *       settle it;
     *   <li>and a thing of its own: it says nothing about itself, or it says something and can be
     *       extended, or it says something and nothing else can be it.
     * </ul>
     */
    static <N, P> WhatStandsHere<N, P> of(Facts<N, P> facts, N node, P where) {
        if (!facts.bound(node)) {
            return new NotBound<>();
        }
        Class<?> type = facts.classOf(node);
        if (AnswerShape.isLeaf(type)) {
            return new ALanguageValue<>();
        }
        if (type.isArray()) {
            return new AnArray<>();
        }
        if (facts.aContainer(node)) {
            return AnswerShape.declaresEquals(type)
                    ? new AContainerOf<>(facts.held(node, where))
                    : new SaysNothingOfItself<>();
        }
        if (!facts.itselfStands(node)) {
            return facts.closedFamily(node)
                    ? new ASumOf<>(facts.arms(node, where))
                    : new NothingClosesIt<>();
        }
        if (!AnswerShape.declaresEquals(type)) {
            return new SaysNothingOfItself<>();
        }
        if (facts.closedFamily(node)) {
            return new AClosedFamily<>(facts.members(node, where), facts.arms(node, where));
        }
        return facts.closesWhatStandsHere(node)
                ? new AClosedValue<>(facts.members(node, where))
                : new NothingClosesIt<>();
    }
}
