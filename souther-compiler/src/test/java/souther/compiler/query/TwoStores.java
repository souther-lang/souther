package souther.compiler.query;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Two stores over one input, compared question by question.
 *
 * <p>What the pair walk needs before it can mean anything, and what it cannot check for itself: the
 * two have to have been asked the same questions. Compared over what they have in common, a question
 * only one of them was put drops out without a word and whatever is written down about the rest goes
 * on holding. So the two key sets are what this looks at first, and a question only one store was put
 * is a place this fell short rather than something it can report on.
 *
 * <p>Its own thing beside {@link Divergence} because it is a different question. That one holds two
 * answers together; this one decides which two answers there are to hold.
 */
final class TwoStores {

    /** One thing in one place, and what the two answers to that question came to there. */
    record Found(Locus.Place place, Divergence.Kind kind) {}

    private TwoStores() {
    }

    /** Everything the two came apart over, and everywhere this could not tell. */
    static Covered<Found> compared(Db one, Db other) {
        Map<Key<?>, Answer<?>> mine = one.everyAnswer();
        Map<Key<?>, Answer<?>> theirs = other.everyAnswer();
        List<Found> found = new ArrayList<>();
        List<Gap> gaps = new ArrayList<>();
        mine.keySet().stream().filter(key -> !theirs.containsKey(key)).forEach(key ->
                gaps.add(new Gap(Gap.Why.A_QUESTION_ONLY_ONE_STORE_WAS_PUT,
                        "only the first store: " + key)));
        theirs.keySet().stream().filter(key -> !mine.containsKey(key)).forEach(key ->
                gaps.add(new Gap(Gap.Why.A_QUESTION_ONLY_ONE_STORE_WAS_PUT,
                        "only the second store: " + key)));
        Set<Key<?>> asked = new HashSet<>(mine.keySet());
        asked.retainAll(theirs.keySet());
        for (Key<?> key : asked) {
            Answer<?> a = mine.get(key);
            Answer<?> b = theirs.get(key);
            if (a.equals(b)) {
                continue;
            }
            switch (Divergence.between(a, b)) {
                case Covered.Whole<Divergence>(List<Divergence> all) -> record(key, all, found);
                case Covered.Partly<Divergence>(List<Divergence> all, List<Gap> fellShort) -> {
                    record(key, all, found);
                    gaps.addAll(fellShort);
                }
            }
        }
        return Covered.of(found, gaps);
    }

    private static void record(Key<?> key, List<Divergence> all, List<Found> into) {
        all.forEach(each -> into.add(new Found(
                each.at().of(key.getClass().getName(), each.cause()), each.kind())));
    }
}
