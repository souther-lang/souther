package souther.compiler.semantics;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

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
        Map<String, Integer> truths = new LinkedHashMap<>();
        List<Map<Integer, Boolean>> reached = new ArrayList<>();
        for (DefinitionCase<A> one : cases) {
            Map<Integer, Boolean> where = new LinkedHashMap<>();
            for (ArgumentsStand<A> stands : one.given()) {
                if (!(stands.left().minus(stands.right())
                        instanceof ExactAnswer.Held<LinearForm<A>>(LinearForm<A> apart))) {
                    return false;
                }
                // `a < b` and `b > a` are one relation, and `a >= b` is its denial.
                String spelled = spelling(apart);
                String turned = spelling(apart.negate());
                Rel rel = spelled.compareTo(turned) <= 0 ? stands.rel() : turnedRound(stands.rel());
                String relation = (spelled.compareTo(turned) <= 0 ? spelled : turned) + " "
                        + rel.orItsDenial();
                int truth = truths.computeIfAbsent(relation, _ -> truths.size());
                Boolean before = where.put(truth, rel == rel.orItsDenial());
                if (before != null && before != (rel == rel.orItsDenial())) {
                    // A case reached where a relation holds and fails is reached nowhere.
                    where = null;
                    break;
                }
            }
            if (where != null) {
                reached.add(where);
            }
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

    /** {@code form} spelled the one way whatever order its terms were met in. */
    private static <A> String spelling(LinearForm<A> form) {
        Map<String, String> terms = new TreeMap<>();
        form.coefs().forEach((atom, weight) -> terms.put(String.valueOf(atom), weight.toString()));
        return terms + " " + form.constant();
    }

    /** {@code rel} with its two sides swapped: {@code a < b} is {@code b > a}. */
    private static Rel turnedRound(Rel rel) {
        return switch (rel) {
            case LT -> Rel.GT;
            case LE -> Rel.GE;
            case GT -> Rel.LT;
            case GE -> Rel.LE;
            case EQ -> Rel.EQ;
            case NE -> Rel.NE;
        };
    }
}
