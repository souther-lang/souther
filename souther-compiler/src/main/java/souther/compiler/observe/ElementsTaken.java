package souther.compiler.observe;

import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.List;

/**
 * Which element was taken at each step inside a sequence to reach one value, outermost step first.
 *
 * <p>The element and not only the value, because a relation between two positions is about one
 * element and not about the two sets: one person under a line and another over it are two readings
 * of a row, and which went with which is the whole of what a pair of positions says. Empty where the
 * position is inside no sequence, which is one value and stands with every other.
 *
 * <p><b>In the order the steps were taken.</b> A step is the path up to and including the step
 * inside a sequence, so the steps one value was reached through run from the outermost sequence to
 * the innermost, and that order is part of what this holds. What a reader builds from them — the
 * readings of a row over its steps, tried up to a bound — depends on it, so it is kept as written
 * rather than left to whatever order a map hands its keys back in.
 *
 * <p>Asked whether two values can be one reading of the row ({@link #agreesWith}) and what element
 * was taken at a step ({@link #elementAt}); nothing here hands the steps over as a map to be walked
 * in whatever order it comes.
 *
 * @param outermostFirst the steps taken, each with the element taken at it
 */
public record ElementsTaken(List<Taken> outermostFirst) {

    /** Nothing taken: the position is inside no sequence. */
    public static final ElementsTaken NONE = new ElementsTaken(List.of());

    /** One step inside a sequence and the element taken at it. */
    public record Taken(TermPath step, int element) {}

    public ElementsTaken {
        outermostFirst = List.copyOf(outermostFirst);
    }

    /** These, and one step more taken inside them. */
    public ElementsTaken and(TermPath step, int element) {
        List<Taken> deeper = new ArrayList<>(outermostFirst);
        deeper.add(new Taken(step, element));
        return new ElementsTaken(deeper);
    }

    /** The element taken at {@code step}, or null where this took no such step. */
    public Integer elementAt(TermPath step) {
        for (Taken each : outermostFirst) {
            if (each.step().equals(step)) {
                return each.element();
            }
        }
        return null;
    }

    /**
     * Whether this and {@code other} can be one reading of the row.
     *
     * <p>Every step the two took together was taken at the same element, and the steps they did not
     * take together are free. Keyed by the step rather than counted, so the rule is one sentence and
     * every case follows from it: two positions under one person agree about the person; a zip code
     * and a phone number under one person agree about the person and not about the address or the
     * phone; two positions under different parameters share nothing and stand with each other
     * however they are spelled; and a position inside no sequence takes no step, so it stands with
     * everything.
     *
     * <p>Counted instead — the first so many elements of one list against the first so many of
     * another — two sibling collections would be zipped, which is a relation neither the row nor the
     * model states.
     */
    public boolean agreesWith(ElementsTaken other) {
        for (Taken each : outermostFirst) {
            Integer beside = other.elementAt(each.step());
            if (beside != null && beside != each.element()) {
                return false;
            }
        }
        return true;
    }
}
