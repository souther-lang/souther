package souther.compiler.inputs;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Supplier;

/**
 * The values made from one value of a walk by a step, by the step, each the one made the first
 * time the step was taken.
 *
 * <p>A body is walked again by every reader of it, from the same values, and a step taken again
 * makes a value equal to the one it made before. Made anew, it is one more value compared whole
 * wherever it is a key, and two equal values compared whole are a walk down everything bound on
 * the way to them; what was asked of the first and kept with it is asked again of the second. The
 * one made before is compared by identity and keeps what was asked of it.
 *
 * <p>For a value nothing in which changes once it is made, so that what a step makes of it is a
 * function of it and of what the step is made with. A step is told apart by which nodes and values
 * those are and never by what they are equal to.
 *
 * @param <T> what a step makes
 */
final class StepsFrom<T> {

    /** One step: how it makes a value, and of what. */
    private record Step(Object how, Object of, Object with) {

        @Override
        public boolean equals(Object other) {
            return other instanceof Step that && how == that.how && of == that.of
                    && with == that.with;
        }

        @Override
        public int hashCode() {
            return (System.identityHashCode(how) * 31 + System.identityHashCode(of)) * 31
                    + System.identityHashCode(with);
        }
    }

    /** What each step made, made when the first step is taken. */
    private volatile Map<Step, T> made;

    /**
     * What the step {@code how}, made with {@code of} and {@code with}, makes: the value
     * {@code make} makes the first time it is taken.
     */
    T madeBy(Object how, Object of, Object with, Supplier<T> make) {
        Map<Step, T> table = made;
        if (table == null) {
            synchronized (this) {
                table = made;
                if (table == null) {
                    table = new ConcurrentHashMap<>();
                    made = table;
                }
            }
        }
        Step step = new Step(how, of, with);
        // Not computeIfAbsent: making a value may take a step from the same one as well.
        T known = table.get(step);
        if (known != null) {
            return known;
        }
        T out = make.get();
        T before = table.putIfAbsent(step, out);
        return before == null ? out : before;
    }
}
