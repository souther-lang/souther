package souther.compiler.coverage;

import java.util.Collection;
import java.util.HashSet;
import java.util.Objects;
import java.util.Set;

/**
 * The walks some run entered and no run took a second element of, which is what shows a list that is
 * one list on every run to hold one element at most.
 *
 * <p>That holds only of runs that came back with an answer. A run that answered went through every
 * walk it entered to the end; one that stopped, or was stopped, may have left a walk before its
 * second element and shows nothing of the list. So the one way to make this is
 * {@link #ofRunsThatAnswered}, and a caller that holds runs which did not answer leaves them out
 * before it calls.
 *
 * @param entered the walks some run that answered entered
 * @param wentOn  the walks some run that answered took a second element of
 */
public record WalkedNoFurther(Set<WalkProbe> entered, Set<WalkProbe> wentOn) {

    /** Nothing seen: no walk is shown to hold one element at most. */
    public static final WalkedNoFurther NOTHING = new WalkedNoFurther(Set.of(), Set.of());

    public WalkedNoFurther {
        entered = Set.copyOf(entered);
        wentOn = Set.copyOf(wentOn);
        if (!entered.containsAll(wentOn)) {
            throw new IllegalArgumentException(
                    "a walk takes a second element only after it is entered");
        }
    }

    /** What the runs in {@code answered}, each one a run that came back with an answer, show. */
    public static WalkedNoFurther ofRunsThatAnswered(Collection<AlignedObservation> answered) {
        Objects.requireNonNull(answered, "the runs that answered are some runs");
        Set<WalkProbe> entered = new HashSet<>();
        Set<WalkProbe> wentOn = new HashSet<>();
        for (AlignedObservation run : answered) {
            for (WalkProbe walk : run.walks()) {
                entered.add(walk);
                if (run.wentOn(walk)) {
                    wentOn.add(walk);
                }
            }
        }
        return new WalkedNoFurther(entered, wentOn);
    }

    /** Whether the list {@code walk} goes over holds one element at most, if it is one list on
     *  every run. */
    public boolean at(WalkProbe walk) {
        return entered.contains(walk) && !wentOn.contains(walk);
    }
}
