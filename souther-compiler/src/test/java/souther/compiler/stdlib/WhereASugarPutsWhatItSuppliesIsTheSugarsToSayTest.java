package souther.compiler.stdlib;

import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A sugar places the arguments it supplies, and a caller writing the rewrite out does not.
 *
 * <p>The arguments an author wrote keep the places they were written in and the supplied ones
 * follow. That is what makes a report about the call the author's: {@code argument 3} of a call of
 * {@code List.fold} is the third of the three they wrote, and the position a combinator's block or
 * a reduction's seed is read at is the position it was written at. A caller handed the constants
 * could put them anywhere, and every one of those readers would then be reading a call the author
 * did not write.
 *
 * <p>So the placing is here, and a sugar that has to supply an argument somewhere else cannot be
 * written down as a {@link Stdlib.Rewrite}. Wanting one is the occasion to say what a report's
 * numbering then means, which is a decision and not a list to lengthen.
 */
class WhereASugarPutsWhatItSuppliesIsTheSugarsToSayTest {

    private static final ValueName.Stdlib.Operation TARGET =
            ValueName.Stdlib.operation("List", "foldFrom");

    /** A sugar of three written arguments that supplies one more. */
    private static final Stdlib.Rewrite FOLD = new Stdlib.Rewrite(TARGET, List.of(0), 3);

    @Test
    void whatWasWrittenKeepsItsPlaceAndWhatIsSuppliedFollows() {
        assertEquals(List.of("step", "seed", "xs", "<0>"),
                FOLD.arguments(List.of("step", "seed", "xs"), constant -> "<" + constant + ">"));
    }

    @Test
    void andASugarSupplyingSeveralKeepsThemInTheOrderItSaysThem() {
        Stdlib.Rewrite two = new Stdlib.Rewrite(TARGET, List.of(7, 9), 1);

        assertEquals(List.of("a", "<7>", "<9>"),
                two.arguments(List.of("a"), constant -> "<" + constant + ">"));
    }

    /**
     * And a call written with another number of arguments is refused rather than placed.
     *
     * <p>Whether a call is the sugar at all is asked before this, of the number of arguments it was
     * written with — the same comparison, and not the same question. That one decides whether the
     * rewrite is taken; this one is the rewrite being handed something it cannot place, which is a
     * caller that took it without asking.
     */
    @Test
    void andACallOfAnotherLengthIsRefusedRatherThanPlaced() {
        assertThrows(IllegalArgumentException.class,
                () -> FOLD.arguments(List.of("step", "seed"), constant -> "<" + constant + ">"));
        assertThrows(IllegalArgumentException.class,
                () -> FOLD.arguments(List.of("step", "seed", "xs", "0"),
                        constant -> "<" + constant + ">"));
    }
}
