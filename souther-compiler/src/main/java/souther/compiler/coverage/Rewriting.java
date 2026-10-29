package souther.compiler.coverage;

import java.util.Collections;
import java.util.SequencedMap;
import java.util.TreeMap;

/**
 * What one run asks the classes to answer with in place of what was written: at the sites of an
 * arm, the part of the sibling that answers there, and at the sites of a walk, the rewrite the walk
 * runs as.
 *
 * <p>One value for both, because a run asks the classes once and {@link Intervention} answers every
 * switch of that run from it. Two runs asking the same thing are one run, which is what a store of
 * the runs already made keys them by.
 *
 * @param arms  the sites of an arm and the part to answer with at each, in the order of the sites
 * @param walks the sites of a walk and the rewrite it runs as at each, in the order of the sites
 */
public record Rewriting(SequencedMap<Integer, Integer> arms,
                        SequencedMap<Integer, WalkRewrite> walks) {

    public Rewriting {
        arms = Collections.unmodifiableSequencedMap(new TreeMap<>(arms));
        walks = Collections.unmodifiableSequencedMap(new TreeMap<>(walks));
    }

    /** Arms answering as siblings, and no walk rewritten. */
    public static Rewriting ofArms(SequencedMap<Integer, Integer> arms) {
        return new Rewriting(arms, new TreeMap<>());
    }

    /** Walks rewritten, and no arm answering as a sibling. */
    public static Rewriting ofWalks(SequencedMap<Integer, WalkRewrite> walks) {
        return new Rewriting(new TreeMap<>(), walks);
    }
}
