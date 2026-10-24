package souther.compiler.regex;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.function.IntPredicate;
import java.util.function.ToLongFunction;

import net.unit8.notation199x.pattern.Automaton;
import net.unit8.notation199x.pattern.CodePoints;

/**
 * A string a machine accepts whose code points come to a number, walked over the machine itself.
 *
 * <p>What a walk of so many symbols can come to at a state is a set of whole numbers, and each
 * step adds a set of code points to it — so a layer of the walk is, at each state, the sums of the
 * layer before shifted by every code point of the step. A set of code points is runs, and runs
 * added to runs are runs, so a layer is held as runs and never as the numbers in them: a step over
 * every digit is one run however many sums it reaches.
 *
 * <p>The string is then read backwards from a state the machine stops at holding the sum: at each
 * layer, a step into the state from one whose sums hold what is left less a code point of the step.
 * The layers are what makes that a choice and never a search, since every state a layer holds a sum
 * at is one a walk from the start reaches with it.
 *
 * <p>A string to be written into a row, so one of the code points a person can be shown
 * ({@link #WRITTEN}); among those, the least of {@code preferred} wherever it has one that leads to
 * the sum, and the least of the step's otherwise.
 */
final class CodePointSums {

    private static final long[] NONE = new long[0];

    /**
     * The code points a string written for a person is made of: every one but the control codes,
     * General_Category=Cc, other than TAB, LF and CR — which {@link Language#someWritten} holds a
     * string to as well. A condition and not a preference, since a string holding one is invisible
     * where it is shown; and Cc is a set Unicode promises never to change.
     */
    private static final CodePoints WRITTEN = CodePoints.EVERYTHING
            .less(CodePoints.between(0, 8))
            .less(CodePoints.between(0x0B, 0x0C))
            .less(CodePoints.between(0x0E, 0x1F))
            .less(CodePoints.between(0x7F, 0x9F));

    private final Automaton machine;
    /** What the code points are to come to, or null where nothing is asked of it. */
    private final Long sum;
    /** The code points a string may hold at an index, where it is held to some. */
    private final Map<Integer, CodePoints> at;
    private final CodePoints preferred;
    /** For each length, at each state, the sums a walk of that length reaches it with: the first of
     *  each run at an even place and its last at the odd one after it, the runs apart and in order,
     *  none past the sum asked for. Where no sum is asked, a state a walk reaches holds the one
     *  run of nought, and what is held is only that it is reached. */
    private final List<long[][]> layers = new ArrayList<>();
    private int work;

    private CodePointSums(Automaton machine, Long sum, Map<Integer, CodePoints> at,
                          CodePoints preferred, int work) {
        this.machine = machine;
        this.sum = sum;
        this.at = at;
        this.preferred = preferred;
        this.work = work;
    }

    /**
     * The string {@code machine} accepts whose code points come to {@code sum}, of a length
     * {@code lengths} admits and no longer than {@code longest}; that none of those is one; or that
     * finding it would take more than {@code work} additions of a run to a run.
     */
    static Language.ComingTo comingTo(Automaton machine, long sum, IntPredicate lengths,
                                      int longest, CodePoints preferred, int work) {
        return holding(machine, Map.of(), sum, lengths, longest, preferred, work);
    }

    /**
     * The same, with the code point at each index {@code at} names one of those it names, and
     * with no sum asked where {@code sum} is null.
     */
    static Language.ComingTo holding(Automaton machine, Map<Integer, CodePoints> at, Long sum,
                                     IntPredicate lengths, int longest, CodePoints preferred,
                                     int work) {
        if (sum != null && sum < 0) {
            return new Language.ComingTo.NoneDoes();
        }
        CodePointSums walking = new CodePointSums(machine, sum, Map.copyOf(at), preferred, work);
        String found = walking.walk(lengths, longest);
        if (found != null) {
            return new Language.ComingTo.Written(found);
        }
        return walking.work < 0 ? new Language.ComingTo.PastTheWork()
                : new Language.ComingTo.NoneDoes();
    }

    /**
     * The least and the greatest number a string {@code machine} accepts comes to, where each step
     * adds no less than {@code leastOf} and no more than {@code mostOf} of the code points it is
     * taken on — what its code points come to, or how many it holds. The greatest is null where a
     * walk to a state it stops at goes round a loop and so comes to no greatest; the whole null
     * where it accepts nothing.
     *
     * <p>The ends and not every number between: a language of {@code a} and {@code c} holds no
     * string coming to 98. What lies between is every number there is and some that are not.
     * Every step adds nought or more, which is what lets the least be read a state at a time.
     */
    static Language.Ends range(Automaton machine, ToLongFunction<CodePoints> leastOf,
                               ToLongFunction<CodePoints> mostOf) {
        boolean[] reaches = machine.reachingSomewhereItStops();
        if (!reaches[Automaton.START]) {
            return null;
        }
        int states = machine.size();
        long[] least = new long[states];
        Arrays.fill(least, Long.MAX_VALUE);
        least[Automaton.START] = 0;
        boolean[] settled = new boolean[states];
        long fewest = Long.MAX_VALUE;
        // Code points are no less than nought, so the least sum at a state is settled once it is
        // the least of those not settled.
        for (int round = 0; round < states; round++) {
            int here = -1;
            for (int state = 0; state < states; state++) {
                if (!settled[state] && reaches[state] && least[state] != Long.MAX_VALUE
                        && (here < 0 || least[state] < least[here])) {
                    here = state;
                }
            }
            if (here < 0) {
                break;
            }
            settled[here] = true;
            if (machine.stopsAt(here)) {
                fewest = Math.min(fewest, least[here]);
            }
            for (Automaton.Step step : machine.stepsFrom(here)) {
                if (reaches[step.to()]) {
                    least[step.to()] = Math.min(least[step.to()],
                            least[here] + leastOf.applyAsLong(step.over()));
                }
            }
        }
        return new Language.Ends(fewest, greatest(machine, reaches, mostOf));
    }

    /**
     * The least and the greatest code point a string {@code machine} accepts holds at
     * {@code index}, or null where it accepts no string that long: of the steps taken from a
     * state a walk of {@code index} code points reaches, to one a walk may still stop after.
     */
    static Language.Ends atIndex(Automaton machine, int index) {
        boolean[] reaches = machine.reachingSomewhereItStops();
        if (!reaches[Automaton.START]) {
            return null;
        }
        int states = machine.size();
        boolean[] here = new boolean[states];
        here[Automaton.START] = true;
        for (int length = 0; length < index; length++) {
            boolean[] next = new boolean[states];
            boolean any = false;
            for (int state = 0; state < states; state++) {
                if (!here[state]) {
                    continue;
                }
                for (Automaton.Step step : machine.stepsFrom(state)) {
                    if (reaches[step.to()] && !step.over().isEmpty()) {
                        next[step.to()] = true;
                        any = true;
                    }
                }
            }
            if (!any) {
                return null;
            }
            here = next;
        }
        long least = Long.MAX_VALUE;
        long most = -1;
        for (int state = 0; state < states; state++) {
            if (!here[state]) {
                continue;
            }
            for (Automaton.Step step : machine.stepsFrom(state)) {
                if (reaches[step.to()] && !step.over().isEmpty()) {
                    least = Math.min(least, step.over().least());
                    most = Math.max(most, step.over().ranges().getLast().to());
                }
            }
        }
        return most < 0 ? null : new Language.Ends(least, most);
    }

    /** The greatest, or null where a walk that can still stop goes round a loop. */
    private static Long greatest(Automaton machine, boolean[] reaches,
                                 ToLongFunction<CodePoints> mostOf) {
        int states = machine.size();
        long[] most = new long[states];
        // 0 not yet walked, 1 being walked, 2 walked.
        int[] seen = new int[states];
        return greatestFrom(machine, Automaton.START, reaches, mostOf, most, seen)
                ? most[Automaton.START] : null;
    }

    private static boolean greatestFrom(Automaton machine, int state, boolean[] reaches,
                                        ToLongFunction<CodePoints> mostOf, long[] most,
                                        int[] seen) {
        if (seen[state] == 2) {
            return true;
        }
        if (seen[state] == 1) {
            return false;
        }
        seen[state] = 1;
        long out = machine.stopsAt(state) ? 0 : Long.MIN_VALUE;
        for (Automaton.Step step : machine.stepsFrom(state)) {
            if (!reaches[step.to()]) {
                continue;
            }
            if (!greatestFrom(machine, step.to(), reaches, mostOf, most, seen)) {
                return false;
            }
            out = Math.max(out, most[step.to()] + mostOf.applyAsLong(step.over()));
        }
        most[state] = out;
        seen[state] = 2;
        return true;
    }

    private String walk(IntPredicate lengths, int longest) {
        int states = machine.size();
        boolean[] reaches = machine.reachingSomewhereItStops();
        long[][] first = new long[states][];
        Arrays.fill(first, NONE);
        if (reaches[Automaton.START]) {
            first[Automaton.START] = new long[] {0, 0};
        }
        layers.add(first);
        for (int length = 0; length <= longest; length++) {
            long[][] layer = layers.get(length);
            // A string shorter than an index asked of holds nothing there, so it holds no code
            // point asked at it.
            if (lengths.test(length) && length > furthestAsked()) {
                for (int state = 0; state < states; state++) {
                    if (machine.stopsAt(state) && holds(layer[state], sum == null ? 0 : sum)) {
                        return readBack(length, state);
                    }
                }
            }
            if (length == longest) {
                break;
            }
            long[][] next = new long[states][];
            Arrays.fill(next, NONE);
            boolean any = false;
            for (int state = 0; state < states; state++) {
                if (layer[state].length == 0) {
                    continue;
                }
                for (Automaton.Step step : machine.stepsFrom(state)) {
                    if (!reaches[step.to()]) {
                        continue;
                    }
                    long[] added = added(layer[state],
                            step.over().and(WRITTEN).and(allowedAt(length)));
                    if (added == null) {
                        return null;
                    }
                    next[step.to()] = joined(next[step.to()], added);
                    any |= added.length > 0;
                }
            }
            // A walk whose every sum is past the one asked for reaches it at no longer length,
            // code points being no less than nought.
            if (!any) {
                return null;
            }
            layers.add(next);
        }
        return null;
    }

    /** The last index a code point is asked at, or below nought where none is. */
    private int furthestAsked() {
        return at.keySet().stream().mapToInt(Integer::intValue).max().orElse(-1);
    }

    /** The code points a string may hold at {@code index}: those {@link #at} names there, or any. */
    private CodePoints allowedAt(int index) {
        return at.getOrDefault(index, CodePoints.EVERYTHING);
    }

    /** The code points read backwards from {@code state} at the {@code length}-th layer. */
    private String readBack(int length, int state) {
        int[] codePoints = new int[length];
        long left = sum == null ? 0 : sum;
        int here = state;
        for (int at = length; at > 0; at--) {
            long[][] before = layers.get(at - 1);
            int chosen = -1;
            int from = -1;
            for (int each = 0; each < before.length && chosen < 0; each++) {
                if (before[each].length == 0) {
                    continue;
                }
                for (Automaton.Step step : machine.stepsFrom(each)) {
                    if (step.to() != here) {
                        continue;
                    }
                    int codePoint = leading(step.over().and(allowedAt(at - 1)), before[each],
                            left);
                    if (codePoint >= 0) {
                        chosen = codePoint;
                        from = each;
                        break;
                    }
                }
            }
            if (chosen < 0) {
                throw new IllegalStateException("a sum the layers hold at a state is reached from"
                        + " the layer before it");
            }
            codePoints[at - 1] = chosen;
            if (sum != null) {
                left -= chosen;
            }
            here = from;
        }
        return new String(codePoints, 0, codePoints.length);
    }

    /**
     * A code point of {@code over} that leaves a sum {@code before} holds of {@code left}, the
     * preferred ones first; negative where none does.
     */
    private int leading(CodePoints over, long[] before, long left) {
        CodePoints leaving = sum == null ? CodePoints.EVERYTHING : CodePoints.NONE;
        for (int at = 0; at < before.length && sum != null; at += 2) {
            long low = left - before[at + 1];
            long high = left - before[at];
            if (high < 0 || low > CodePoints.LAST) {
                continue;
            }
            leaving = leaving.or(CodePoints.between((int) Math.max(low, 0),
                    (int) Math.min(high, CodePoints.LAST)));
        }
        CodePoints taken = over.and(WRITTEN).and(leaving);
        if (taken.isEmpty()) {
            return -1;
        }
        CodePoints liked = taken.and(preferred);
        return liked.isEmpty() ? taken.least() : liked.least();
    }

    /** The sums {@code runs} come to with a code point of {@code over} added, up to the one asked
     *  for; null past the work allowed. */
    private long[] added(long[] runs, CodePoints over) {
        if (sum == null) {
            if (--work < 0) {
                return null;
            }
            return over.isEmpty() ? NONE : new long[] {0, 0};
        }
        List<long[]> out = new ArrayList<>();
        for (int at = 0; at < runs.length; at += 2) {
            for (CodePoints.Range range : over.ranges()) {
                if (--work < 0) {
                    return null;
                }
                long low = runs[at] + range.from();
                long high = Math.min(runs[at + 1] + range.to(), sum);
                if (low <= high) {
                    out.add(new long[] {low, high});
                }
            }
        }
        return normalised(out);
    }

    private static long[] joined(long[] one, long[] other) {
        if (one.length == 0) {
            return other;
        }
        List<long[]> both = new ArrayList<>();
        for (long[] runs : List.of(one, other)) {
            for (int at = 0; at < runs.length; at += 2) {
                both.add(new long[] {runs[at], runs[at + 1]});
            }
        }
        return normalised(both);
    }

    private static long[] normalised(List<long[]> runs) {
        runs.sort((a, b) -> Long.compare(a[0], b[0]));
        List<long[]> out = new ArrayList<>();
        for (long[] each : runs) {
            long[] last = out.isEmpty() ? null : out.get(out.size() - 1);
            if (last != null && each[0] <= last[1] + 1) {
                last[1] = Math.max(last[1], each[1]);
            } else {
                out.add(new long[] {each[0], each[1]});
            }
        }
        long[] flat = new long[out.size() * 2];
        for (int at = 0; at < out.size(); at++) {
            flat[2 * at] = out.get(at)[0];
            flat[2 * at + 1] = out.get(at)[1];
        }
        return flat;
    }

    private static boolean holds(long[] runs, long number) {
        for (int at = 0; at < runs.length; at += 2) {
            if (runs[at] <= number && number <= runs[at + 1]) {
                return true;
            }
        }
        return false;
    }
}
