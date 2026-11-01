package souther.compiler.meaning;

import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.TermPath;
import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;

/**
 * One case of where a line decides, as a row is asked it, and the cases it is said for.
 *
 * <p>Past {@link WhereEachLineDecides#MOST_CASES} the cases where a line decides are said as one
 * condition, holding exactly where one of them does, so that a reader composing rows looks along one
 * way rather than more than it can. That bounds how many are said and not what they are. A line
 * decides in a case where a row on each side of it can stand in that case, since the two rows then
 * differ in the line alone; under a condition said for several cases, the row on one side and the
 * row on the other may each stand in a case of its own, and the line turns nothing between them. So
 * the cases themselves are kept beside the condition, for a reader asking whether the line decides
 * in any one of them.
 *
 * @param condition what a row is asked to be for the line to decide there
 * @param standsFor the cases {@code condition} is said for, which hold together exactly where it
 *                  does: {@code condition} alone, for a case said by itself
 */
public record DecidingCase(Proposition condition, Cases standsFor) {

    public DecidingCase {
        Objects.requireNonNull(condition, "a case is some condition, if only nothing");
        Objects.requireNonNull(standsFor, "a case is said for some cases, if only itself");
    }

    /** A case said by itself. */
    public static DecidingCase alone(Proposition condition) {
        return new DecidingCase(condition, new Cases.One(condition));
    }

    /**
     * This and {@code other}, which are said by one condition, as one case.
     *
     * <p>Two cases said by one condition are not one case: one may stand for itself alone and the
     * other for several, and whether the line decides is asked of each case either stands for. So
     * what they are together is said here, and nowhere else. Where either stands for itself, so do
     * the two: rows on both sides of the line in a case the other stands for are rows on both sides
     * of it in the whole condition, which is that one case. Otherwise they stand for every case
     * either stood for.
     */
    DecidingCase and(DecidingCase other) {
        if (!condition.equals(other.condition)) {
            throw new IllegalArgumentException("two cases are one where they are said by one"
                    + " condition: " + condition + " and " + other.condition);
        }
        if (saidAlone()) {
            return this;
        }
        if (other.saidAlone()) {
            return other;
        }
        return equals(other) ? this
                : new DecidingCase(condition, new Cases.EachOf(List.of(standsFor, other.standsFor)));
    }

    /**
     * {@code cases}, one for each condition they are said by, in the order the conditions first
     * come: those said by one condition taken as one ({@link #and}).
     */
    static List<DecidingCase> oneForEachCondition(List<DecidingCase> cases) {
        Map<Proposition, DecidingCase> out = new LinkedHashMap<>();
        cases.forEach(each -> out.merge(each.condition, each, DecidingCase::and));
        return List.copyOf(out.values());
    }

    /**
     * {@code cases} checked to be one for each condition they are said by.
     *
     * <p>A case is read by its condition wherever a row is asked to be in it, so two said by one
     * condition would be two readings no reader tells apart, and what one of them stood for would
     * go unasked. Whoever gathers cases takes them as one ({@link #oneForEachCondition}); a
     * gathering that forgot is stopped here rather than read as one of them.
     */
    public static List<DecidingCase> eachByItsOwnCondition(List<DecidingCase> cases) {
        Set<Proposition> seen = new HashSet<>();
        for (DecidingCase each : cases) {
            if (!seen.add(each.condition)) {
                throw new IllegalArgumentException("two cases said by one condition, which are"
                        + " one case: " + each.condition);
            }
        }
        return List.copyOf(cases);
    }

    /**
     * {@code cases} said as the cases where a line decides are: one for each condition, each by
     * itself up to {@link WhereEachLineDecides#MOST_CASES}, and past that as one, standing for each
     * of them.
     *
     * <p>Said the same way whichever way the cases came to be these: a line read with few cases
     * where it decides and the same line left with as few once the others are dropped are read in
     * the same cases, each under its own condition. And counted over the whole line, however many
     * cases said for several they came out of.
     */
    public static List<DecidingCase> saidInAsFewAsMay(List<DecidingCase> cases) {
        List<DecidingCase> each = oneForEachCondition(cases);
        return each.size() <= WhereEachLineDecides.MOST_CASES ? each : List.of(someOneOf(each));
    }

    /**
     * {@code cases} said as one: some one of them holding, standing for each of them.
     *
     * <p>What every one of them holds is said once, ahead of what tells them apart. What every case
     * of a line holds is often most of each — the rest of the statement holding, which may be as
     * long as the statement — so written beside each it would be the condition many times over.
     */
    static DecidingCase someOneOf(List<DecidingCase> cases) {
        Set<Proposition> everyOne = new LinkedHashSet<>(conjunctsOf(cases.getFirst().condition));
        cases.forEach(each -> everyOne.retainAll(conjunctsOf(each.condition)));
        List<Proposition> apart = cases.stream()
                .map(each -> Proposition.all(conjunctsOf(each.condition).stream()
                        .filter(part -> !everyOne.contains(part)).toList()))
                .toList();
        List<Proposition> said = new ArrayList<>(everyOne);
        said.add(Proposition.any(apart));
        return new DecidingCase(Proposition.all(said), eachOf(cases));
    }

    /** What {@code condition} holds all of together: its parts, where it is a conjunction. */
    private static List<Proposition> conjunctsOf(Proposition condition) {
        return condition instanceof Proposition.All all ? all.parts() : List.of(condition);
    }

    /** The cases each of {@code cases} stands for, any one of them. */
    static Cases eachOf(List<DecidingCase> cases) {
        return cases.size() == 1 ? cases.getFirst().standsFor()
                : new Cases.EachOf(cases.stream().map(DecidingCase::standsFor).toList());
    }

    /**
     * This case where {@code also} holds as well, standing for each of its cases where it does.
     *
     * <p>Where this case has a value of the row be one case, {@code also} is read with the value
     * that case: what it says of the value being another case comes out the way that answers. An
     * arm of a choice this case is not in has no say in it, read or not.
     */
    DecidingCase meeting(Proposition also) {
        for (Proposition part : conjunctsOf(condition)) {
            if (part instanceof Proposition.InCases(DecisionSubject.AnInput(TermPath at),
                    CasesLeft cases, boolean held, var _)
                    && held && cases.atoms().size() == 1
                    && at.steps().stream().noneMatch(step -> step instanceof TermPath.Step.Element
                            || step instanceof TermPath.Step.Key)) {
                also = WhereEachLineDecides.assuming(also, new DecisionSubject.AnInput(at),
                        cases.atoms());
            }
        }
        if (also instanceof Proposition.Always(boolean holds) && holds) {
            return this;
        }
        Proposition met = Proposition.all(List.of(condition, also));
        return saidAlone() ? alone(met)
                : new DecidingCase(met, new Cases.Together(List.of(standsFor, new Cases.One(also))));
    }

    /** Whether this is said for no case but its own, so that asking its cases asks it again. */
    public boolean saidAlone() {
        return standsFor instanceof Cases.One(Proposition one) && one.equals(condition);
    }

    /**
     * Cases, each a condition: what a case said for several is made of.
     *
     * <p>Kept as they were taken apart and not written out. Where a line decides inside a
     * quantifier is a case of each thing around it taken together, and written out that is every
     * way of choosing one of each, which grows as their product; held as the choices, a reader
     * asking each case can stop choosing as soon as what it has chosen so far leaves no row on one
     * side of the line, since a case chosen further holds fewer rows than that.
     */
    public sealed interface Cases {

        /** One case. */
        record One(Proposition condition) implements Cases {

            public One {
                Objects.requireNonNull(condition, "a case is some condition");
            }
        }

        /** Any one of these. None is no case at all. */
        record EachOf(List<Cases> alternatives) implements Cases {

            public EachOf {
                alternatives = List.copyOf(alternatives);
            }

            /** Cases share what follows from a choice, so a hash walking them is as long as they
             *  are many: what is shared here is the number of alternatives. */
            @Override
            public int hashCode() {
                return 31 * alternatives.size() + 1;
            }

            @Override
            public boolean equals(Object other) {
                return other instanceof EachOf && same(this, (Cases) other, new IdentityHashMap<>());
            }

            @Override
            public String toString() {
                return describe(this);
            }
        }

        /** One case of each of these, holding together. None is the case where nothing is asked. */
        record Together(List<Cases> factors) implements Cases {

            public Together {
                factors = List.copyOf(factors);
            }

            /** As {@link EachOf#hashCode}: what is shared here is the number of factors. */
            @Override
            public int hashCode() {
                return 37 * factors.size() + 2;
            }

            @Override
            public boolean equals(Object other) {
                return other instanceof Together
                        && same(this, (Cases) other, new IdentityHashMap<>());
            }

            @Override
            public String toString() {
                return describe(this);
            }
        }

        /**
         * Cases nobody took apart, the taking apart stopped at {@code stoppedAt}: more cases than
         * are taken apart ({@link CompositionBudget#CASES_A_LINE_IS_TAKEN_APART_INTO}), or more
         * steps than a statement is read in
         * ({@link CompositionBudget#STEPS_A_STATEMENT_IS_READ_IN}). Which of them hold a row on each
         * side of the line is something nobody worked out.
         */
        record NotTakenApart(CompositionBudget stoppedAt) implements Cases {

            public NotTakenApart {
                Objects.requireNonNull(stoppedAt, "a taking apart stops at some figure");
            }
        }

        /** The cases these conditions say, each a conjunction of its parts, sharing what the ones
         *  beside each other begin with. */
        static Cases ofConjunctions(List<List<Proposition>> each) {
            List<Cases> alternatives = new ArrayList<>();
            Map<Proposition, List<List<Proposition>>> byFirst = new LinkedHashMap<>();
            for (List<Proposition> one : each) {
                if (one.isEmpty()) {
                    alternatives.add(new Together(List.of()));
                } else {
                    byFirst.computeIfAbsent(one.getFirst(), _ -> new ArrayList<>())
                            .add(one.subList(1, one.size()));
                }
            }
            byFirst.forEach((first, rests) -> alternatives.add(new Together(
                    List.of(new One(first), ofConjunctions(rests)))));
            return alternatives.size() == 1 ? alternatives.getFirst() : new EachOf(alternatives);
        }

        /**
         * What a fold makes of each kind of cases, given what it made of the cases inside.
         *
         * <p>The cases are a graph and not a tree: the state a choice leaves is one value every
         * way to it shares ({@link WhereEachLineDecides}), so the ways of choosing grow as the
         * product of the choices while the cases that hold them grow as their sum. A reader that
         * walks them as a tree walks the product.
         *
         * <p>Nor may what it makes of a case be a copy of what it made of the cases inside: a case
         * held twice by one case is the same result twice, and a result that holds those of the
         * cases inside by copying them is as long as the ways to the case. A result holds the ones
         * made of the cases inside it, or something of a size that does not grow with them.
         */
        interface Fold<R> {

            R one(One one);

            R eachOf(EachOf node, List<R> alternatives);

            R together(Together node, List<R> factors);

            R notTakenApart(NotTakenApart notTakenApart);
        }

        /**
         * What {@code by} makes of these, each of the cases they hold worked out once however many
         * ways lead to it.
         *
         * <p>The one place that walks the cases and the only one that may: every question asked of
         * all of them, and every comparison and every rendering, goes through it, so that none
         * is a tree walk of a graph. What a fold makes of a case is a function of the case, so it
         * is the same whichever way the case was reached.
         */
        default <R> R fold(Fold<R> by) {
            return fold(by, new IdentityHashMap<>());
        }

        /** The same, taking {@code worked} as what has been made of the cases already, and adding
         *  what is made here to it: for a reader that folds the cases more than once. */
        default <R> R fold(Fold<R> by, Map<Cases, R> worked) {
            R known = worked.get(this);
            if (known != null) {
                return known;
            }
            R made = switch (this) {
                case One one -> by.one(one);
                case EachOf each -> by.eachOf(each, foldAll(each.alternatives(), by, worked));
                case Together group -> by.together(group, foldAll(group.factors(), by, worked));
                case NotTakenApart notTakenApart -> by.notTakenApart(notTakenApart);
            };
            worked.put(this, Objects.requireNonNull(made, "a fold makes something of every case"));
            return made;
        }

        /**
         * How many cases hold each case of these, each case counted once however many ways lead
         * to it: a case held by one case is only in that one's way, and one held by more is shared
         * by every way that goes through them.
         */
        default Map<Cases, Integer> references() {
            Map<Cases, Integer> held = new IdentityHashMap<>();
            countHolds(this, held);
            return held;
        }

        /** Each figure some of these were stopped at where they were never taken apart. */
        default Set<CompositionBudget> notTakenApartAt() {
            return notTakenApartAt(new IdentityHashMap<>());
        }

        private static <R> List<R> foldAll(List<Cases> cases, Fold<R> by, Map<Cases, R> worked) {
            List<R> made = new ArrayList<>(cases.size());
            for (Cases one : cases) {
                made.add(one.fold(by, worked));
            }
            return made;
        }

        /**
         * Where some one of these holds, written as they were taken apart — or nothing where some
         * of them were never taken apart, which nothing writes.
         *
         * <p>Read off the cases themselves and not off the condition they were said as, so that
         * the two cannot come to say different things: what is said of a case's parts where the
         * line stands under a case of a value is said of each case, part by part, and the
         * condition is said as one part.
         *
         * <p>Nothing either where there are more than {@code most} ways of choosing a case. The
         * condition is as long as they are many however the cases share what follows from a
         * choice, so it is not written: a reader that wanted it was told so here and not left to
         * count the ways first.
         */
        default Optional<Proposition> holdingInSome(long most) {
            if (waysOfChoosing(most) > most) {
                return Optional.empty();
            }
            return fold(new Fold<Optional<Proposition>>() {

                @Override
                public Optional<Proposition> one(One one) {
                    return Optional.of(one.condition());
                }

                @Override
                public Optional<Proposition> eachOf(EachOf node,
                                                    List<Optional<Proposition>> alternatives) {
                    return joined(alternatives, false);
                }

                @Override
                public Optional<Proposition> together(Together node,
                                                      List<Optional<Proposition>> factors) {
                    return joined(factors, true);
                }

                @Override
                public Optional<Proposition> notTakenApart(NotTakenApart notTakenApart) {
                    return Optional.empty();
                }
            });
        }

        private static Optional<Proposition> joined(List<Optional<Proposition>> each,
                                                    boolean every) {
            List<Proposition> parts = new ArrayList<>();
            for (Optional<Proposition> holding : each) {
                if (holding.isEmpty()) {
                    return Optional.empty();
                }
                parts.add(holding.get());
            }
            return Optional.of(every ? Proposition.all(parts) : Proposition.any(parts));
        }

        /**
         * How many ways there are of choosing one case of these, or {@code past} and one more
         * where there are more than {@code past}.
         *
         * <p>Counted off the choices as they stand, without choosing: any one of several is as
         * many ways as each of them has together, and one of each of several holding together is
         * as many as theirs multiplied. Cases nobody took apart are one way, which ends there.
         */
        default long waysOfChoosing(long past) {
            return fold(new Fold<Long>() {

                @Override
                public Long one(One one) {
                    return 1L;
                }

                @Override
                public Long eachOf(EachOf node, List<Long> alternatives) {
                    long ways = 0;
                    for (long these : alternatives) {
                        ways = Math.min(past + 1, ways + these);
                    }
                    return ways;
                }

                @Override
                public Long together(Together node, List<Long> factors) {
                    long ways = 1;
                    for (long these : factors) {
                        if (these == 0) {
                            return 0L;
                        }
                        ways = Math.min(past + 1, ways * these);
                    }
                    return ways;
                }

                @Override
                public Long notTakenApart(NotTakenApart notTakenApart) {
                    return 1L;
                }
            });
        }

        /** These, each one case of them said as {@code each} says it — no case at all where it
         *  says none. */
        default Cases eachSaid(Function<Proposition, Cases> each) {
            return fold(new Fold<Cases>() {

                @Override
                public Cases one(One one) {
                    return each.apply(one.condition());
                }

                @Override
                public Cases eachOf(EachOf node, List<Cases> alternatives) {
                    return new EachOf(alternatives);
                }

                @Override
                public Cases together(Together node, List<Cases> factors) {
                    return new Together(factors);
                }

                @Override
                public Cases notTakenApart(NotTakenApart notTakenApart) {
                    return notTakenApart;
                }
            });
        }

        /**
         * Each figure some of these were stopped at where they were never taken apart.
         *
         * <p>Written in the cases and not worked out by choosing among them, so it costs a visit
         * to each case and no more, and a reader that has run out of steps may ask it.
         *
         * @param worked what has been made of the cases already, for a reader that asks of
         *               several cases that share some
         */
        default Set<CompositionBudget> notTakenApartAt(Map<Cases, Set<CompositionBudget>> worked) {
            return fold(new Fold<Set<CompositionBudget>>() {

                @Override
                public Set<CompositionBudget> one(One one) {
                    return Set.of();
                }

                @Override
                public Set<CompositionBudget> eachOf(EachOf node,
                                                     List<Set<CompositionBudget>> alternatives) {
                    return union(alternatives);
                }

                @Override
                public Set<CompositionBudget> together(Together node,
                                                       List<Set<CompositionBudget>> factors) {
                    return union(factors);
                }

                @Override
                public Set<CompositionBudget> notTakenApart(NotTakenApart notTakenApart) {
                    return Set.of(notTakenApart.stoppedAt());
                }
            }, worked);
        }

        private static Set<CompositionBudget> union(List<Set<CompositionBudget>> these) {
            Set<CompositionBudget> out = EnumSet.noneOf(CompositionBudget.class);
            these.forEach(out::addAll);
            return out.isEmpty() ? Set.of() : Collections.unmodifiableSet(out);
        }

        /**
         * Whether {@code one} and {@code other} are the same cases, as a graph.
         *
         * <p>A pair of cases is compared once. Compared as trees, two graphs that are equal and
         * not the same object are as long to compare as they have ways of choosing, which is the
         * product of their choices; a comparison stops at the first difference, so a pair that
         * has been met again is one that was equal when it was met.
         */
        private static boolean same(Cases one, Cases other, Map<Cases, Set<Cases>> met) {
            if (one == other) {
                return true;
            }
            if (!met.computeIfAbsent(one, _ -> Collections.newSetFromMap(new IdentityHashMap<>()))
                    .add(other)) {
                return true;
            }
            return switch (one) {
                case One(var condition) -> other instanceof One(var that)
                        && condition.equals(that);
                case NotTakenApart(var stoppedAt) -> other instanceof NotTakenApart(var that)
                        && stoppedAt == that;
                case EachOf(var alternatives) -> other instanceof EachOf(var that)
                        && sameAll(alternatives, that, met);
                case Together(var factors) -> other instanceof Together(var that)
                        && sameAll(factors, that, met);
            };
        }

        private static boolean sameAll(List<Cases> these, List<Cases> those,
                                       Map<Cases, Set<Cases>> met) {
            if (these.size() != those.size()) {
                return false;
            }
            for (int at = 0; at < these.size(); at++) {
                if (!same(these.get(at), those.get(at), met)) {
                    return false;
                }
            }
            return true;
        }

        /**
         * These written out once each: a case that more than one case holds is written in full
         * where it first comes and by its number after, so that what is written is as long as
         * the cases are many and not as their ways of choosing.
         */
        private static String describe(Cases root) {
            Map<Cases, Integer> held = new IdentityHashMap<>();
            countHolds(root, held);
            return describe(root, held, new IdentityHashMap<>());
        }

        private static void countHolds(Cases cases, Map<Cases, Integer> held) {
            if (held.merge(cases, 1, Integer::sum) > 1) {
                return;
            }
            switch (cases) {
                case EachOf(var alternatives) -> alternatives.forEach(one -> countHolds(one, held));
                case Together(var factors) -> factors.forEach(one -> countHolds(one, held));
                case One _, NotTakenApart _ -> { }
            }
        }

        private static String describe(Cases cases, Map<Cases, Integer> held,
                                       Map<Cases, Integer> numbered) {
            Integer number = numbered.get(cases);
            if (number != null) {
                return "#" + number;
            }
            String label = "";
            if (held.get(cases) > 1 && !(cases instanceof One || cases instanceof NotTakenApart)) {
                number = numbered.size() + 1;
                numbered.put(cases, number);
                label = "#" + number + "=";
            }
            return label + switch (cases) {
                case One(var condition) -> "One[" + condition + "]";
                case NotTakenApart(var stoppedAt) -> "NotTakenApart[" + stoppedAt + "]";
                case EachOf(var alternatives) -> "EachOf" + describeAll(alternatives, held,
                        numbered);
                case Together(var factors) -> "Together" + describeAll(factors, held, numbered);
            };
        }

        private static String describeAll(List<Cases> each, Map<Cases, Integer> held,
                                          Map<Cases, Integer> numbered) {
            StringBuilder out = new StringBuilder("[");
            for (Cases one : each) {
                out.append(out.length() > 1 ? ", " : "").append(describe(one, held, numbered));
            }
            return out.append(']').toString();
        }
    }
}
