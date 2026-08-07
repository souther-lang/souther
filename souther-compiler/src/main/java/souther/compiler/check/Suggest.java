package souther.compiler.check;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.List;

/**
 * "Did you mean" hints for unknown names. When a name the checker cannot resolve is a near-miss of
 * one that is in scope, the error carries the likely intended name, so a typo reads as a typo. The
 * closeness bound is Levenshtein distance ≤ 2 and strictly less than the name's length, so a short
 * name does not match every candidate.
 *
 * <p>What "near" measures is one thing across the compiler and the documentation tools: an edit
 * distance, not a containment. How near is near enough is not — a class identifier and a section
 * anchor are not the same length — so {@link #nearest} takes its bound from the caller while the
 * measure stays here.
 */
public final class Suggest {

    /** The bound an unknown identifier is matched under. */
    private static final int NEAR_ENOUGH = 2;

    private Suggest() {
    }

    /**
     * The candidates within {@code bound} edits of {@code name}, closest first, at most
     * {@code limit} of them.
     *
     * <p>A candidate must also be further than its own length is short — a two-letter name would
     * otherwise be within two edits of everything and suggest whatever came first.
     */
    public static List<String> nearest(String name, Collection<String> candidates, int bound, int limit) {
        record Near(String candidate, int distance) {}
        List<Near> near = new ArrayList<>();
        for (String candidate : candidates) {
            if (candidate.equals(name)) {
                continue;
            }
            int d = distance(name, candidate);
            if (d <= bound && d < name.length()) {
                near.add(new Near(candidate, d));
            }
        }
        return near.stream()
                .sorted(Comparator.comparingInt(Near::distance).thenComparing(Near::candidate))
                .limit(limit)
                .map(Near::candidate)
                .toList();
    }

    /** {@code " (did you mean `X`?)"} for the closest candidate within bound, or {@code ""}. */
    public static String hint(String name, Collection<String> candidates) {
        String best = candidate(name, candidates);
        return best == null ? "" : " (did you mean `" + best + "`?)";
    }

    /** The closest in-scope candidate to {@code name} within the closeness bound, or {@code null}.
     * The structured form of {@link #hint}, for a diagnostic's {@code suggestion} field. */
    public static String candidate(String name, Collection<String> candidates) {
        String best = null;
        int bestDistance = Integer.MAX_VALUE;
        for (String candidate : candidates) {
            if (candidate.equals(name)) {
                continue;
            }
            int d = distance(name, candidate);
            if (d < bestDistance) {
                bestDistance = d;
                best = candidate;
            }
        }
        if (best != null && bestDistance <= NEAR_ENOUGH && bestDistance < name.length()) {
            return best;
        }
        return null;
    }

    /** Levenshtein edit distance (insert/delete/substitute), on Unicode code points. */
    static int distance(String a, String b) {
        int[] ca = a.codePoints().toArray();
        int[] cb = b.codePoints().toArray();
        int[] prev = new int[cb.length + 1];
        int[] cur = new int[cb.length + 1];
        for (int j = 0; j <= cb.length; j++) {
            prev[j] = j;
        }
        for (int i = 1; i <= ca.length; i++) {
            cur[0] = i;
            for (int j = 1; j <= cb.length; j++) {
                int sub = prev[j - 1] + (ca[i - 1] == cb[j - 1] ? 0 : 1);
                cur[j] = Math.min(sub, Math.min(prev[j] + 1, cur[j - 1] + 1));
            }
            int[] tmp = prev;
            prev = cur;
            cur = tmp;
        }
        return prev[cb.length];
    }
}
