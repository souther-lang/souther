package souther.compiler.meaning;

import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.HashSet;
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

    /** This case where {@code also} holds as well, standing for each of its cases where it does. */
    DecidingCase meeting(Proposition also) {
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
        }

        /** One case of each of these, holding together. None is the case where nothing is asked. */
        record Together(List<Cases> factors) implements Cases {

            public Together {
                factors = List.copyOf(factors);
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
         * Where some one of these holds, written as they were taken apart — or nothing where some
         * of them were never taken apart, which nothing writes.
         *
         * <p>Read off the cases themselves and not off the condition they were said as, so that
         * the two cannot come to say different things: what is said of a case's parts where the
         * line stands under a case of a value is said of each case, part by part, and the
         * condition is said as one part.
         */
        default Optional<Proposition> holdingInSome() {
            return switch (this) {
                case One(var condition) -> Optional.of(condition);
                case EachOf(var alternatives) -> joined(alternatives, false);
                case Together(var factors) -> joined(factors, true);
                case NotTakenApart _ -> Optional.empty();
            };
        }

        private static Optional<Proposition> joined(List<Cases> each, boolean every) {
            List<Proposition> parts = new ArrayList<>();
            for (Cases one : each) {
                Optional<Proposition> holding = one.holdingInSome();
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
            return switch (this) {
                case One _, NotTakenApart _ -> 1;
                case EachOf(var alternatives) -> {
                    long ways = 0;
                    for (Cases one : alternatives) {
                        ways = Math.min(past + 1, ways + one.waysOfChoosing(past));
                    }
                    yield ways;
                }
                case Together(var factors) -> {
                    long ways = 1;
                    for (Cases one : factors) {
                        long these = one.waysOfChoosing(past);
                        if (these == 0) {
                            yield 0;
                        }
                        ways = Math.min(past + 1, ways * these);
                    }
                    yield ways;
                }
            };
        }

        /** These, each one case of them said as {@code each} says it — no case at all where it
         *  says none. */
        default Cases eachSaid(Function<Proposition, Cases> each) {
            return switch (this) {
                case One(var condition) -> each.apply(condition);
                case EachOf(var alternatives) ->
                        new EachOf(alternatives.stream().map(one -> one.eachSaid(each)).toList());
                case Together(var factors) ->
                        new Together(factors.stream().map(one -> one.eachSaid(each)).toList());
                case NotTakenApart notTakenApart -> notTakenApart;
            };
        }
    }
}
