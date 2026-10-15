package souther.compiler.meaning;

import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
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

    /** {@code cases} said as one: some one of them holding, standing for each of them. */
    static DecidingCase someOneOf(List<DecidingCase> cases) {
        return new DecidingCase(
                Proposition.any(cases.stream().map(DecidingCase::condition).toList()),
                eachOf(cases));
    }

    /** The cases each of {@code cases} stands for, any one of them. */
    static Cases eachOf(List<DecidingCase> cases) {
        return new Cases.EachOf(cases.stream().map(DecidingCase::standsFor).toList());
    }

    /** This case where {@code also} holds as well, standing for each of its cases where it does. */
    DecidingCase meeting(Proposition also) {
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
         * More cases than are taken apart
         * ({@link CompositionBudget#CASES_A_LINE_IS_TAKEN_APART_INTO}). Which of them hold a row on
         * each side of the line is something nobody worked out.
         */
        record MoreThanWereTakenApart() implements Cases {}

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

        /** These, each one case of them said as {@code each} says it — no case at all where it
         *  says none. */
        default Cases eachSaid(Function<Proposition, Cases> each) {
            return switch (this) {
                case One(var condition) -> each.apply(condition);
                case EachOf(var alternatives) ->
                        new EachOf(alternatives.stream().map(one -> one.eachSaid(each)).toList());
                case Together(var factors) ->
                        new Together(factors.stream().map(one -> one.eachSaid(each)).toList());
                case MoreThanWereTakenApart more -> more;
            };
        }
    }
}
