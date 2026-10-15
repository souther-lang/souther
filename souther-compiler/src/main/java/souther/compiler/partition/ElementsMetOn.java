package souther.compiler.partition;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhereAnApplicationIsMade;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * Which elements of the input a run makes a comparison on, where the comparison stands inside
 * closures an operation applies to the elements of containers the input holds, or in the body of a
 * helper that walks one by calling itself.
 *
 * <p>Not whether a run makes the comparison at all, which is what stood on the way to it says and a
 * run through it records. This is which element: {@code List.any(x -> x > 0, xs)} applies its
 * closure to an element only where no element before it held, so on {@code [1, 0]} the comparison
 * is made on the first element and never on the second. A row standing at {@code 0} through its
 * second element stands where no run compared anything, and the run having got an answer out of the
 * comparison on the first element does not change that.
 *
 * <p>Said of each container a reading may choose an element of, because that is the only way the
 * answer turns on which element: a reading of a row that chose no element of a container is about
 * none of them, and a run recorded through the comparison is one through it. So what is not known
 * is said of the container it is not known of, and a reading choosing no element there is not
 * left undecided by it. And never every element for want of knowing: where which elements is not
 * known, that is said, with why.
 *
 * <p>Said here and read off each reading of a row, because the order is the row's: which element
 * stops the operation is what the elements before it hold.
 *
 * @param levels what is known of each container the comparison's closures are applied over, the
 *               outermost first. None: a run that gets as far as the comparison makes it on every
 *               element a reading can name
 * @param made   what a row meets for the comparison to be made through it at all, beyond a run
 *               having been recorded through it: the way to the call of a helper whose body it is,
 *               where that body is run by other calls too and a run recorded through it may have
 *               been another call's
 */
public record ElementsMetOn(List<Level> levels, Proposition made) {

    public ElementsMetOn {
        levels = List.copyOf(levels);
        Objects.requireNonNull(made, "a comparison is made somewhere, or anywhere");
    }

    /** What is known of one container the comparison's closures are applied over. */
    public sealed interface Level {

        /**
         * Made on an element of {@code container} only where no element before it stopped the
         * operation.
         *
         * @param stops what, said of an element of it, stops the operation there: what the
         *              closure answers where it stops at the first that holds, and its denial
         *              where it stops at the first that fails. A subject under
         *              {@code container[*]} in it is that element's
         */
        record StopsAt(TermPath container, Proposition stops) implements Level {

            public StopsAt {
                Objects.requireNonNull(container, "an operation stops short in some container");
                Objects.requireNonNull(stops, "and at something");
            }
        }

        /**
         * Which elements of {@code container} it is made on is not said, for this reason: an
         * operation picking one out, or some, by what nothing here reads.
         */
        record NotSaidOf(TermPath container, ReadingGap why) implements Level {

            public NotSaidOf {
                Objects.requireNonNull(container, "what is not said is of some container");
                Objects.requireNonNull(why, "and not said for a reason");
            }
        }

        /**
         * Which elements it is made on is not said, of whichever container a reading chooses an
         * element of: the closure is applied over something that is no container at a position,
         * or how often it is applied is not said at all.
         */
        record NotSaidAnywhere(ReadingGap why) implements Level {

            public NotSaidAnywhere {
                Objects.requireNonNull(why, "what is not said is not said for a reason");
            }
        }
    }

    /** Every element a reading can name, which is what a comparison inside no such closure is. */
    public static final ElementsMetOn EVERY =
            new ElementsMetOn(List.of(), WhereAnApplicationIsMade.nothingAsked());

    /** The same, inside one more closure that stops in {@code container} at what {@code stops}
     *  says of an element. */
    ElementsMetOn stoppingIn(TermPath container, Proposition stops) {
        return deeper(new Level.StopsAt(container, stops));
    }

    /** The same, inside one more closure made on elements of {@code container} nothing says. */
    ElementsMetOn notSaidOf(TermPath container, ReadingGap why) {
        return deeper(new Level.NotSaidOf(container, why));
    }

    /** The same, inside one more closure made on elements nothing says of any container. */
    ElementsMetOn notSaidAnywhere(ReadingGap why) {
        return deeper(new Level.NotSaidAnywhere(why));
    }

    private ElementsMetOn deeper(Level level) {
        List<Level> deeper = new ArrayList<>(levels);
        deeper.add(level);
        return new ElementsMetOn(deeper, made);
    }

    /** The same, made only where a row also meets {@code way}. */
    ElementsMetOn madeWhere(Proposition way) {
        return new ElementsMetOn(levels, WhereAnApplicationIsMade.past(made, way));
    }

    /**
     * The same, made wherever a run was recorded through it: where nothing but one call runs the
     * body the comparison is in, a run recorded there is that call's.
     */
    ElementsMetOn madeWhereverRecorded() {
        return new ElementsMetOn(levels, WhereAnApplicationIsMade.nothingAsked());
    }
}
