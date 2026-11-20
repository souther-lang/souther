package souther.compiler.partition;

import souther.compiler.inputs.TermPath;

import java.util.List;
import java.util.Objects;

/**
 * Where the numbers a value a run works out come to come from, as the reader of numbers found
 * them ({@link WorkedOutToReachIt#numbersOf}): a number written, a place of the input, one of
 * several values, or anything else worked out. Each carries the numbers it was read to come to.
 *
 * <p>Said so that a way to the value can narrow them: a place by what the way states of it, and
 * one of several values by what it leaves of each. What is worked out otherwise is no place a
 * way states anything of, and keeps what it was read to come to ({@link WhatAWayLeavesOfAValue}).
 *
 * <p>An account of an upper bound and nothing else. That a value may come to a number says
 * nothing of a run that gets it there: the candidates of {@link OneOf} are what it may be, and
 * not what some run makes it.
 */
sealed interface WhereAValueComesFrom {

    /** The numbers the value was read to come to, wherever it is reached. */
    FormRange range();

    /** A number written, or worked out of numbers written. */
    record Fixed(FormRange range) implements WhereAValueComesFrom {

        public Fixed {
            Objects.requireNonNull(range, "the number written");
        }
    }

    /**
     * What a place of the input holds, as the arms the value was read past leave it: an element
     * of a container where the place stands inside one.
     */
    record AtAPlace(TermPath place, FormRange range) implements WhereAValueComesFrom {

        public AtAPlace {
            Objects.requireNonNull(place, "a place of the input");
            Objects.requireNonNull(range, "what the place holds");
        }
    }

    /**
     * One of {@code candidates}, whichever a run takes: either arm of a choice, any value a name
     * was given, an element of a list written out, or what a walk keeping its seed or an element
     * comes to. Two or more, or one where only one is left.
     *
     * @param range what any of them comes to, worked out once when this is made: an answer the
     *              reader of numbers keeps, asked as often as the value is read
     */
    record OneOf(List<WhereAValueComesFrom> candidates, FormRange range)
            implements WhereAValueComesFrom {

        public OneOf {
            candidates = List.copyOf(candidates);
            Objects.requireNonNull(range, "what any of them comes to");
            if (candidates.isEmpty()) {
                throw new IllegalArgumentException("a value is one of some candidates");
            }
        }

        public OneOf(List<WhereAValueComesFrom> candidates) {
            this(candidates, hullOf(candidates));
        }

        private static FormRange hullOf(List<WhereAValueComesFrom> candidates) {
            FormRange hull = candidates.getFirst().range();
            for (WhereAValueComesFrom each : candidates.subList(1, candidates.size())) {
                hull = hull.hull(each.range());
            }
            return hull;
        }
    }

    /** Worked out otherwise: an operation, a call of the library, a field a rule bounds. */
    record Derived(FormRange range) implements WhereAValueComesFrom {

        public Derived {
            Objects.requireNonNull(range, "what it was read to come to");
        }
    }

    /** One of {@code candidates}, or the one itself where there is only one. */
    static WhereAValueComesFrom oneOf(List<WhereAValueComesFrom> candidates) {
        return candidates.size() == 1 ? candidates.getFirst() : new OneOf(candidates);
    }
}
