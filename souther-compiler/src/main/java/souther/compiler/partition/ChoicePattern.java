package souther.compiler.partition;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.function.Predicate;

/**
 * A set of the choices of one group, stated as the outcomes some of its factors take and the rest
 * left either way.
 *
 * <p>The choices of a group are a product of its factors, and a set of them that stands in one
 * state is most often a product too: every outcome of the factors it leaves open, the one outcome
 * it names of each of the others. Said that way the set costs one entry however many choices are in
 * it, and a set that is a single choice names every factor, which is the entry a list of choices
 * would have had.
 *
 * <p>Exact in both directions. A pattern holds a choice only where the choice is one the group has
 * (a choice whose factors leave a position nothing is no choice) and is in the state the pattern is
 * of, so the patterns of one state cover the choices of that state once each and nothing else.
 *
 * @param fixed the outcome taken at each factor, in the order of the group's factors, or null where
 *              the pattern holds the factor either way
 * @param count how many choices of the group the pattern holds
 */
public record ChoicePattern(List<Integer> fixed, int count) {

    public ChoicePattern {
        fixed = Collections.unmodifiableList(new ArrayList<>(fixed));
        if (count < 1) {
            throw new IllegalArgumentException("a pattern holds a choice or it is not one: " + count);
        }
    }

    /** A pattern and the state every choice in it is in. */
    public record Found<S>(ChoicePattern pattern, S state) {
    }

    /**
     * The patterns of the choices of a group whose state {@code reported} accepts.
     *
     * <p>Read off the factors in their order, as a tree: the first factor is the first branching. A
     * node is one pattern when every choice below it is a choice of the group in one state, and
     * is otherwise split on the next factor — so what two groups of decisions have in common is
     * said once, and what sets a choice apart is said where it is.
     *
     * @param stateAt the state of the {@code index}th choice of the group, or null where it is no
     *                choice. Two choices are in one state where the states are equal.
     */
    public static <S> List<Found<S>> of(List<Integer> widths, List<S> stateAt,
                                        Predicate<S> reported) {
        Objects.requireNonNull(widths, "patterns are of some group");
        int factors = widths.size();
        int[] stride = new int[factors];
        int size = 1;
        for (int factor = 0; factor < factors; factor++) {
            stride[factor] = size;
            size *= widths.get(factor);
        }
        if (stateAt.size() != size) {
            throw new IllegalArgumentException("a group of " + size + " choices has "
                    + stateAt.size() + " states");
        }
        int[][] below = new int[factors + 1][];
        below[factors] = new int[] {0};
        for (int factor = factors - 1; factor >= 0; factor--) {
            int width = widths.get(factor);
            int[] inner = below[factor + 1];
            int[] offsets = new int[width * inner.length];
            for (int outcome = 0; outcome < width; outcome++) {
                for (int i = 0; i < inner.length; i++) {
                    offsets[outcome * inner.length + i] = outcome * stride[factor] + inner[i];
                }
            }
            below[factor] = offsets;
        }
        List<Found<S>> out = new ArrayList<>();
        walk(widths, stateAt, reported, stride, below, 0, new Integer[factors], 0, out);
        return List.copyOf(out);
    }

    private static <S> void walk(List<Integer> widths, List<S> stateAt,
                                 Predicate<S> reported, int[] stride, int[][] below, int depth,
                                 Integer[] fixed, int base, List<Found<S>> out) {
        int[] offsets = below[depth];
        S first = stateAt.get(base + offsets[0]);
        boolean one = first != null && reported.test(first);
        for (int i = 1; one && i < offsets.length; i++) {
            one = first.equals(stateAt.get(base + offsets[i]));
        }
        if (one) {
            Integer[] taken = fixed.clone();
            for (int factor = depth; factor < taken.length; factor++) {
                taken[factor] = null;
            }
            out.add(new Found<>(new ChoicePattern(Arrays.asList(taken), offsets.length), first));
            return;
        }
        if (depth == fixed.length) {
            return;
        }
        int width = widths.get(depth);
        for (int outcome = 0; outcome < width; outcome++) {
            fixed[depth] = outcome;
            walk(widths, stateAt, reported, stride, below, depth + 1, fixed,
                    base + outcome * stride[depth], out);
        }
        fixed[depth] = null;
    }
}
