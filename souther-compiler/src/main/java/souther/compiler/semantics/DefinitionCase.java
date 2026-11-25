package souther.compiler.semantics;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * One case of a piecewise definition: the number it answers, written in the arguments, and what
 * the arguments stand as for it to be reached.
 *
 * <p>The answer is a form of the arguments: one of them, as {@code Int.min} answers one of the two
 * it was given, or arithmetic over them, as {@code Int.abs} answers {@code 0 - n} where {@code n}
 * is below nought.
 *
 * <p>Generic in the word for an argument, as {@link ElementLineage} is: authored, a case names its
 * arguments as the fact writes them; held to the library, as the declaration has them.
 *
 * @param <A> the word for an argument of the operation
 */
public record DefinitionCase<A>(LinearForm<A> answers, List<ArgumentsStand<A>> given) {

    /** The most relations a definition's cases are read over together, as truths. */
    private static final int MOST_RELATIONS = 12;

    public DefinitionCase {
        java.util.Objects.requireNonNull(answers, "a case answers a number of the arguments");
        given = List.copyOf(given);
    }

    /**
     * Whether this case answers one of the values the operation was given, as itself, reached by
     * how two of them stand — which is an arm of a choice between the values at a call.
     */
    public boolean choosesAnArgument() {
        return ArgumentsStand.theArgument(answers) != null && given.stream().allMatch(stands ->
                ArgumentsStand.theArgument(stands.left()) != null
                        && ArgumentsStand.theArgument(stands.right()) != null);
    }

    /**
     * Whether some one of {@code cases} is reached however the arguments stand: every way the
     * relations they are reached under can come out reaches one of them.
     *
     * <p>Each relation read as a truth of its own, and a relation and its denial as one truth: a
     * list of cases covering every way those truths come out covers every way the arguments can
     * stand, since a way the arguments stand is one of those ways. Where it does not, the cases
     * are no definition of the operation, whatever each of them answers where it is reached — and
     * read as one, a value they leave out would be read as one of them.
     */
    public static <A> boolean coverEveryWay(List<DefinitionCase<A>> cases) {
        Map<Set<Set<Said<A>>>, Integer> truths = new LinkedHashMap<>();
        List<Map<Integer, Boolean>> reached = new ArrayList<>();
        for (DefinitionCase<A> one : cases) {
            Map<Integer, Boolean> where = new LinkedHashMap<>();
            for (ArgumentsStand<A> stands : one.given()) {
                if (!(stands.left().minus(stands.right())
                        instanceof ExactAnswer.Held<LinearForm<A>>(LinearForm<A> apart))) {
                    return false;
                }
                // `a < b` and `b > a` are one relation, and `a >= b` is its denial: one truth,
                // the rows where it holds and the rows where it fails, each however it is said.
                Set<Said<A>> holds = waysOfSaying(apart, stands.rel());
                Set<Said<A>> fails = waysOfSaying(apart, stands.rel().denied());
                int truth = truths.computeIfAbsent(Set.copyOf(List.of(holds, fails)),
                        _ -> truths.size());
                boolean held = onTheSideOfLess(holds);
                Boolean before = where.put(truth, held);
                if (before != null && before != held) {
                    // A case reached where a relation holds and fails is reached nowhere.
                    where = null;
                    break;
                }
            }
            if (where != null) {
                reached.add(where);
            }
        }
        // A case reached under no relation is reached however the arguments stand, which is all
        // this asks, and the relations the cases beside it are reached under take nothing from it.
        if (reached.stream().anyMatch(Map::isEmpty)) {
            return true;
        }
        if (truths.size() > MOST_RELATIONS) {
            return false;
        }
        for (long way = 0; way < 1L << truths.size(); way++) {
            long taken = way;
            boolean some = reached.stream().anyMatch(where -> where.entrySet().stream()
                    .allMatch(each -> (((taken >> each.getKey()) & 1) == 1) == each.getValue()));
            if (!some) {
                return false;
            }
        }
        return true;
    }

    /** One way of saying which rows a relation of the arguments holds at: a form of them held
     *  against nought. */
    private record Said<A>(LinearForm<A> form, Rel rel) { }

    /** Every way of saying the rows at which {@code form rel 0}: as it is, and turned round. */
    private static <A> Set<Said<A>> waysOfSaying(LinearForm<A> form, Rel rel) {
        return Set.copyOf(List.of(new Said<>(form, rel), new Said<>(form.negate(), rel.turned())));
    }

    /**
     * Which of a truth's two sides {@code rows} is, the same however either is said: the side
     * some way of saying holds below nought or at it. Of {@code f < 0} and {@code f >= 0}, the
     * first, which is also {@code -f > 0}; of {@code f <= 0} and {@code f > 0}, the second, which
     * is also {@code -f < 0}; of {@code f == 0} and {@code f != 0}, the first.
     */
    private static <A> boolean onTheSideOfLess(Set<Said<A>> rows) {
        return rows.stream().anyMatch(said -> said.rel() == Rel.LT || said.rel() == Rel.EQ);
    }
}
