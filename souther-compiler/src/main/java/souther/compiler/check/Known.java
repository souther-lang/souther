package souther.compiler.check;

import souther.compiler.collect.AppendOnly;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.ClosedStates;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.OrderedIntervals;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.values.Allowance;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * What holds where the walk stands: numeric relations, predicates known to hold or to fail, relations
 * known of every element of a container, which cases a value an arm or a condition on the way
 * settled may still be, and the terms an assumption named — which is what makes a
 * computed value one a clause may be read against. Threaded functionally through the walk, as the
 * domain alone once was.
 *
 * <p>Beside it is {@link Unguarded}, the same reading with nothing a condition on the path settled.
 * Both are refined by the same acts and differ only in which acts reach both, so a clause that comes
 * out refuted can be asked which of the two refuted it. That is what a violation is explained by: one
 * the unguarded reading already refutes holds wherever the construction stands, and one only the full
 * reading refutes took something more than the values to settle. Which something is not recorded, so
 * it is not claimed either.
 *
 * <p>Equal by its parts, and its parts by which states they are: the numbers a state holds and the
 * terms its assumptions named are compared as the objects they are and not by what they hold
 * ({@link AppendOnly}). So two of these are equal where they were made of the same states, and
 * nothing asks it whether two paths know alike — a reader with that question asks what each knows.
 *
 * <p>And the conditions on the path that hold as one of their parts, which no domain here holds
 * ({@link #oneOf}). Kept as they were written and taken apart only by a reader that has a question
 * the parts answer and the whole does not: a domain holding each part of each of them would be one
 * state per way of choosing a part, multiplied at every such condition the path passes, whether or
 * not anything below was ever asked of them.
 */
record Known(ConstraintState<FactSubject> constraints, List<Quantified> quantified,
                     AppendOnly<FactSubject, Boolean> spoken, Unguarded unguarded,
                     Map<FactSubject, CasesLeft> cases, Choices oneOf) {

    Known {
        cases = Map.copyOf(cases);
    }

    /**
     * The conditions held here as one of their parts, and one way through all of them.
     *
     * <p>Held as a line each one is put on top of, for the reason the spoken terms are told on: a
     * path holds one more of them at each such condition it passes, and copying what it held at
     * each would cost the square of the path. On top, so that what came to be held since a count
     * was taken is read off the top without walking what was held before it.
     *
     * <p>The way is a state with one part taken in of every condition it holds — the ones held
     * here, and the ones taking a part of them came to hold — which nothing had shown to reach
     * nothing when it was made. It is what lets a condition taken in later be asked of one state,
     * rather than of every way of choosing a part of each: a way that takes the new condition in
     * and still reaches something is a run that gets past it. It answers only that. That the
     * conditions leave no way at all is answered by looking for one over what is known
     * ({@link Predicates#assumeCond}), never by this one failing — what is known may by then hold
     * more than the way does, and a way that knew less is a way that admits more, which is the safe
     * side for a "yes" and no ground for a "no". Null where the looking was given up: the path is
     * then one nothing has shown to reach nothing, and is not looked along again.
     *
     * <p>{@code tries} is how many more parts the looking may take in alone along this path, across
     * every time it looks ({@link #PARTS_A_PATH_LOOKS_THROUGH}).
     */
    record Choices(ChoiceLine held, Known wayIn, int tries, DeclinedLine declined) {

        /**
         * How many parts of the choices a path holds are taken in alone along one path, looking
         * for a way through them where the way kept dies.
         *
         * <p>Counted for the path and not per look: a way that dies at one guard after another is
         * looked for at each, and a count kept per look would have the path pay the whole of it
         * again every time. Set by what a part read costs here, which is a reading of the domain of
         * every value on the path, and not by how many parts a reading of a condition's meaning
         * takes alone ({@link CompositionBudget#ALTERNATIVES_A_PATH_TRIES}),
         * whose parts are read against far less.
         *
         * <p>A figure of this check's and not of the composing stage: reaching it stops no search
         * a report says anything about. The path is then one nothing has shown to reach nothing,
         * which is what it is taken to be without the looking, and no construction on it is judged
         * differently from one on a path that holds no choice.
         */
        static final int PARTS_A_PATH_LOOKS_THROUGH = 64;

        static final Choices NONE = new Choices(null, null, PARTS_A_PATH_LOOKS_THROUGH, null);

        int count() {
            return held == null ? 0 : held.count();
        }
    }

    /**
     * A choice read by its meaning that more than one of its parts was left to when it was taken in,
     * and the bindings and places it was read under ({@link MeaningAssumptions}).
     *
     * <p>Not one of the parts holding: which part holds is no fact of the path. What the path comes
     * to know afterwards may rule parts out, and the choice is then taken in as the part left, or
     * as nothing reached where none is. The bindings are the ones where the choice stands, as for
     * {@link OneOf}.
     *
     * <p>Every one a path passes is kept, so what it rules out does not turn on how many choices
     * stand between a choice and the condition that singles out its part. What bounds the work is
     * the count of parts a reading takes alone ({@link MeaningAssumptions}), which says so where
     * it is reached.
     *
     * <p>Equal only to itself, for the reason {@link OneOf} is.
     */
    record Declined(Proposition.Any any, Denotations at, MeaningAssumptions.InputPlaces places) {

        @Override
        public boolean equals(Object other) {
            return this == other;
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(this);
        }
    }

    /** One choice left undecided, on top of the ones left before it. */
    record DeclinedLine(Declined last, DeclinedLine before) {}

    /** One condition held, on top of the ones held before it, and how many that is in all. */
    record ChoiceLine(OneOf last, ChoiceLine before, int count) {}

    /**
     * A condition that holds here as one of its parts, and the bindings it was read under.
     *
     * <p>Not one of the parts, and not what the parts have in common: {@code y >= 0.5 || y <= -0.5}
     * says each value of {@code y} is in one of two ranges, and the range they span holds
     * {@code 0}. What the condition says is said by taking each part in alone, under what else is
     * known where the question is asked ({@link Predicates#eachWayOf}).
     *
     * <p>The bindings are the ones in force where the condition stands, because that is where its
     * names mean what they mean. A reader further in has entered more of them and a name it holds
     * may be another value.
     *
     * <p>Equal only to itself, as the other states this holds are: which condition was taken in is
     * which reading took it, and the same guard read twice is two of these. Compared by what they
     * hold, two would also walk the trees they were read out of.
     */
    record OneOf(ClauseExpr.Joined of, Denotations at) {

        @Override
        public boolean equals(Object other) {
            return this == other;
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(this);
        }
    }

    /** What holds of the values here whatever the path did — what a type guarantees of a value and
     * what a name was given. It carries no quantifiers and no spoken terms: those decide which
     * clauses are read at all, and both readings are asked about the same clauses. */
    record Unguarded(ConstraintState<FactSubject> constraints) {

        Unguarded taking(LinearForm<FactSubject> f, Rel rel, Map<FactSubject, Granularity> kinds) {
            return new Unguarded(constraints.taking(f, rel, kinds));
        }

        Unguarded taking(FactSubject key, boolean positive) {
            return new Unguarded(constraints.taking(key, positive));
        }

        NumericDomain<FactSubject> numbers() {
            return constraints.numbers();
        }

        PredicateFacts<FactSubject> facts() {
            return constraints.facts();
        }
    }

    /** The relations between numbers this state holds. Handed out for what only an interval can
     * answer — a bound is read off one and off nothing else — and for nothing about the state as a
     * whole. Whether a value exists and whether a path is reached are both
     * {@link ConstraintState#isBottom}, and neither is assembled from this. */
    NumericDomain<FactSubject> numbers() {
        return constraints.numbers();
    }

    /** The predicates this state has settled, read the same way and for the same reason. */
    PredicateFacts<FactSubject> facts() {
        return constraints.facts();
    }

    /**
     * Whether the conditions that hold here cannot all hold, so nothing stands where this does.
     *
     * <p>Asked of the whole state ({@link ConstraintState#isBottom}) and not of a domain, because a
     * clause reaches whatever domain has a word for it: guards that settle a predicate both ways
     * leave the predicates contradictory and every number untouched, and a reader that asked the
     * numbers would walk that path and report the construction standing on it. That is a report
     * about a value the program never builds.
     *
     * <p>No flag of its own, for the same reason. A second record of the answer is a second thing to
     * keep in step, and the first domain added without touching it would put the two out of
     * agreement — which is the shape this question already came apart along once.
     */
    boolean reachesNothing() {
        return constraints.isBottom();
    }

    /** How far a fact reaches: a value's type and a name's binding say something wherever that value
     * is named, and a condition says it only on the path it guards. */
    enum Held { OF_THE_VALUE, ON_THE_PATH }

    /**
     * Nothing known, each domain taken from here working out what its rules leave for itself.
     *
     * <p>For a reader that holds no engine. A walk an engine makes starts at
     * {@link PathEngine#nothingKnown}, which lends one walk's closures to the next.
     */
    static Known top() {
        return top(ClosedStates.NONE);
    }

    /**
     * Nothing known, with what the numbers leave worked out through {@code closures}, which every
     * fact taken in afterwards keeps.
     */
    static Known top(ClosedStates closures) {
        return new Known(ConstraintState.top(FactSubject.inOneOrder(), closures), List.of(),
                AppendOnly.empty(),
                new Unguarded(ConstraintState.top(FactSubject.inOneOrder(), closures)), Map.of(),
                Choices.NONE);
    }

    /** This, with {@code f rel 0} taken as holding as far as {@code held} reaches. */
    Known taking(LinearForm<FactSubject> f, Rel rel, Held held, Map<FactSubject, Granularity> kinds) {
        return new Known(constraints.taking(f, rel, kinds), quantified, spoken,
                held == Held.OF_THE_VALUE ? unguarded.taking(f, rel, kinds) : unguarded, cases,
                oneOf);
    }

    /**
     * This, with the values a declaration leaves the names of one value taken in.
     *
     * <p>Of the value and not of the path: what a declaration's rules admit is true wherever a
     * value of it is named. Taken in as a reading of the values rather than as numbers —
     * {@code value == 1 || value == 3} leaves a gap between two values that no range holds, and it
     * is the values beside the ranges a path takes in that show an arm written for the gap is one
     * nothing enters ({@link ConstraintState#isBottom}).
     *
     * <p>Met with what is known rather than read into it. Every value a walk enters says what its
     * declaration leaves it, so this is a conjunction of many such readings, one per value, and a
     * conjunction is what {@link ConstraintState#meet} is: readings about different values are held
     * apart and pay nothing for each other.
     */
    Known admitting(Confinement.Worked<FactSubject> read, Allowance<FactSubject> sets) {
        ConstraintState<FactSubject> values =
                ConstraintState.top(FactSubject.inOneOrder()).takingRead(read, sets);
        return new Known(constraints.meet(values, sets), quantified, spoken,
                new Unguarded(unguarded.constraints().meet(values, sets)), cases, oneOf);
    }

    /**
     * This, with the values a condition leaves a number taken in, on the path only.
     *
     * <p>Met with what is known as {@link #admitting} meets a declaration's values, and kept from
     * the reading that ignores the path: a condition says it, so a contradiction it takes part in
     * is one the guards on the way make and not one the values make wherever they are named.
     */
    Known holdingOnThePath(Confinement.Worked<FactSubject> read, Allowance<FactSubject> sets) {
        ConstraintState<FactSubject> values =
                ConstraintState.top(FactSubject.inOneOrder()).takingRead(read, sets);
        return new Known(constraints.meet(values, sets), quantified, spoken, unguarded, cases,
                oneOf);
    }

    /**
     * This, with {@code bounded} taken as holding on the path, on the orders {@code on} says the
     * positions are counted by.
     *
     * <p>For a comparison against a place on an order where there is no sum to say it as — two
     * strings do not add. A condition says it, so it reaches the path and not the value.
     */
    Known bounding(OrderedIntervals<FactSubject> bounded, Map<FactSubject, Carrier> on) {
        return new Known(constraints.taking(bounded, on), quantified, spoken, unguarded, cases,
                oneOf);
    }

    /** This, with the predicate {@code key} taken as holding — or as failing, where {@code positive}
     * is false — as far as {@code held} reaches. */
    Known taking(FactSubject key, boolean positive, Held held) {
        return new Known(constraints.taking(key, positive), quantified, spoken,
                held == Held.OF_THE_VALUE ? unguarded.taking(key, positive) : unguarded, cases,
                oneOf);
    }

    /**
     * This, with the value {@code value} one of {@code left} on this path, or reaching nothing where
     * what the path already left it holds none of them.
     *
     * <p>On the path only. Which case a value is, is what an arm or a condition on the way settled,
     * and a value's type says nothing of it.
     *
     * <p>What was left before and {@code left} are met ({@link CasesLeft#meet}). Two answers of
     * unlike kinds — an optional's carriers beside a sum's cases — are about two values that were
     * named alike, and they say nothing of each other, so the first is kept.
     */
    Known inCases(FactSubject value, CasesLeft left) {
        CasesLeft was = cases.get(value);
        if (was == null) {
            Map<FactSubject, CasesLeft> more = new HashMap<>(cases);
            more.put(value, left);
            return new Known(constraints, quantified, spoken, unguarded, more, oneOf);
        }
        if (!was.atoms().getFirst().getClass().equals(left.atoms().getFirst().getClass())) {
            return this;
        }
        CasesLeft both = was.meet(left);
        if (both == null) {
            return reachingNothing();
        }
        if (both.equals(was)) {
            return this;
        }
        Map<FactSubject, CasesLeft> narrowed = new HashMap<>(cases);
        narrowed.put(value, both);
        return new Known(constraints, quantified, spoken, unguarded, narrowed, oneOf);
    }

    /**
     * This, where the conditions on the path cannot all hold, so nothing here is reached.
     *
     * <p>Said of the state and not lodged in a domain ({@link ConstraintState#shownToHoldNothing}):
     * what shows it is a reading of the cases an operation is defined in, and no interval and no
     * predicate holds that argument. The reading that ignores the path is left as it was — it is the
     * guards that cannot all hold, not the values that fail, and a construction under them is one
     * the program never builds rather than one it builds wrongly.
     */
    Known reachingNothing() {
        return new Known(constraints.shownToHoldNothing(), quantified, spoken, unguarded, cases,
                oneOf);
    }

    /**
     * This, with each of {@code terms} recorded as one an assumption on this path named. It is
     * recorded where the assumption is made rather than searched for afterwards: what a guard
     * spoke about is known exactly then, and reading it back out of a domain would mean matching
     * key text, which is how a term that merely reads like another gets mistaken for it.
     *
     * <p>Told on to what this was told rather than copied from it ({@link AppendOnly}): a path names
     * something new at most of the rules it takes, and copying what it had named at each of those
     * costs the square of the path.
     */
    Known speaking(Collection<FactSubject> terms) {
        AppendOnly<FactSubject, Boolean> all = spoken;
        for (FactSubject term : terms) {
            if (!all.contains(term)) {
                all = all.with(term, true);
            }
        }
        return all == spoken ? this
                : new Known(constraints, quantified, all, unguarded, cases, oneOf);
    }

    /** Whether an assumption on this path named {@code term}. */
    boolean speaksOf(FactSubject term) {
        return spoken.contains(term);
    }

    Known and(List<Quantified> more) {
        if (more.isEmpty()) {
            return this;
        }
        List<Quantified> all = new ArrayList<>(quantified);
        all.addAll(more);
        return new Known(constraints, List.copyOf(all), spoken, unguarded, cases, oneOf);
    }

    /**
     * This, with {@code condition} holding as one of its parts, on the path only.
     *
     * <p>On the path for the reason every condition is: it is the guard that says it, and a value
     * named anywhere else is not held to it.
     */
    Known holdingOneOf(OneOf condition) {
        return new Known(constraints, quantified, spoken, unguarded, cases,
                new Choices(new ChoiceLine(condition, oneOf.held(), oneOf.count() + 1),
                        oneOf.wayIn(), oneOf.tries(), oneOf.declined()));
    }

    /** The choices read by their meaning that no part has yet been settled for, oldest first. */
    List<Declined> declinedChoices() {
        List<Declined> out = new ArrayList<>();
        for (DeclinedLine at = oneOf.declined(); at != null; at = at.before()) {
            out.add(at.last());
        }
        return out.reversed();
    }

    /** This, with {@code declined} as the choices read by their meaning left undecided. */
    Known leavingUndecided(List<Declined> declined) {
        DeclinedLine line = null;
        for (Declined each : declined) {
            line = new DeclinedLine(each, line);
        }
        return new Known(constraints, quantified, spoken, unguarded, cases,
                new Choices(oneOf.held(), oneOf.wayIn(), oneOf.tries(), line));
    }

    /** This, with {@code choice} left undecided after the ones left before it. */
    Known leavingUndecided(Declined choice) {
        return new Known(constraints, quantified, spoken, unguarded, cases,
                new Choices(oneOf.held(), oneOf.wayIn(), oneOf.tries(),
                        new DeclinedLine(choice, oneOf.declined())));
    }

    /** The conditions held here as one of their parts, in the order they were taken in. */
    List<OneOf> heldAsOneOfTheirParts() {
        return heldSince(0);
    }

    /** How many conditions are held here as one of their parts. */
    int heldCount() {
        return oneOf.count();
    }

    /** The conditions held here past the first {@code count}, in the order they were taken in. */
    List<OneOf> heldSince(int count) {
        List<OneOf> out = new ArrayList<>();
        for (ChoiceLine at = oneOf.held(); at != null && at.count() > count; at = at.before()) {
            out.add(at.last());
        }
        return out.reversed();
    }

    /** Whether any condition is held here as one of its parts. */
    boolean holdsAChoice() {
        return oneOf.held() != null;
    }

    /**
     * A state with one part taken in of every condition it holds, which nothing had shown to reach
     * nothing when it was made — this state itself where none is held — or null where the looking
     * for one was given up ({@link Choices}).
     */
    Known wayIn() {
        return holdsAChoice() ? oneOf.wayIn() : this;
    }

    /** How many more parts looking for a way may take in alone along this path ({@link Choices}). */
    int triesLeft() {
        return oneOf.tries();
    }

    /** This, with {@code way} as the way through the conditions it holds — null where the looking
     *  was given up — and {@code tries} left to look with ({@link Choices}). */
    Known throughWay(Known way, int tries) {
        return new Known(constraints, quantified, spoken, unguarded, cases,
                new Choices(oneOf.held(), way, tries, oneOf.declined()));
    }

    /**
     * This, speaking of exactly what {@code other} speaks of.
     *
     * <p>For a state read from {@code other} to answer what follows from a condition and not what
     * its author named ({@link Predicates#eachWayOf}): what it knows of the values is its own, and
     * which values the path has said something of is {@code other}'s.
     */
    Known speakingAs(Known other) {
        return other.spoken == spoken ? this
                : new Known(constraints, quantified, other.spoken, unguarded, cases, oneOf);
    }
}
