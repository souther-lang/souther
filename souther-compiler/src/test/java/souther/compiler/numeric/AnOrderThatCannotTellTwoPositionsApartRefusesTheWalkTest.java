package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.List;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An order over an atom domain is a coarsening of equality, and the direction it does not promise is
 * established where a walk needs it.
 *
 * <p><b>Which is the whole of what the type says.</b> {@link CanonicalOrder} promises that two
 * positions that are one compare as one, and does not promise the converse: what a domain can see of
 * a position may be less than what tells two of them apart. A walk cannot live with that — two
 * positions it takes for one are one weighed twice and one never weighed — so the walk refuses the
 * pair rather than choosing between them, and that is the one place the missing direction is
 * settled.
 *
 * <p>Said here because everything that walks a form rests on it and nothing else says it. Written
 * only at {@link CanonicalForm#entriesIn}, the refusal would be a rule the next caller to sort by
 * one of these has to remember.
 */
class AnOrderThatCannotTellTwoPositionsApartRefusesTheWalkTest {

    /** An order that reads less of a position than its equality does, which is what a domain whose
     *  positions are told apart by something no writing carries comes to. */
    private static final CanonicalOrder<String> BY_ITS_FIRST_LETTER =
            (one, other) -> Character.compare(one.charAt(0), other.charAt(0));

    @Test
    void anOrderThatTellsThemApartWalksThemInIt() {
        assertEquals(List.of("ant", "bee", "cow"),
                BY_ITS_FIRST_LETTER.walking(List.of("cow", "ant", "bee"), Function.identity()));
    }

    /**
     * And two it cannot tell apart are refused, with both of them named.
     *
     * <p>Not chosen between. Which of the two a sort leaves first is what the sort happened to do,
     * so an answer built on it would be about the walk — and naming one of them would tell two
     * callers that wrote one thing two ways two different things about the same pair.
     */
    @Test
    void twoItCannotTellApartAreRefused() {
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> BY_ITS_FIRST_LETTER.walking(List.of("ant", "ape"), Function.identity()));

        assertTrue(refused.getMessage().contains("ant") && refused.getMessage().contains("ape"),
                "the refusal names the pair it could not tell apart: " + refused.getMessage());
    }

    /**
     * And the same pair is refused whichever way round it arrives.
     *
     * <p>The reason the refusal is worth having: the two writings below are one thing to walk, and
     * an order that answered for one of them and not the other would be the very thing this refuses
     * on behalf of.
     */
    @Test
    void andTheSamePairIsRefusedWhicheverWayRoundItArrives() {
        String oneWay = assertThrows(IllegalStateException.class,
                () -> BY_ITS_FIRST_LETTER.walking(List.of("ant", "ape"), Function.identity()))
                .getMessage();
        String theOther = assertThrows(IllegalStateException.class,
                () -> BY_ITS_FIRST_LETTER.walking(List.of("ape", "ant"), Function.identity()))
                .getMessage();

        assertEquals(oneWay, theOther);
    }

    /**
     * And two that really are one position are not a pair.
     *
     * <p>What the law does promise, from the other side: an order is a coarsening of equality, so
     * two positions that are one compare as one — and a walk meeting them has met one position
     * twice rather than two it cannot tell apart.
     */
    @Test
    void twoThatAreOnePositionAreNotRefused() {
        assertEquals(List.of("ant", "ant"),
                BY_ITS_FIRST_LETTER.walking(List.of("ant", "ant"), Function.identity()));
    }

    /**
     * And a domain that wrote its order as its own comparison is held to the same thing.
     *
     * <p>Which is why there is no lift from {@link Comparable} at large. Java does not ask a
     * comparison to agree with its equality, and the classes that do not are ordinary: two decimals
     * written to different scales are two values that compare as one. A domain that says its order
     * is its positions' own comparison has said something this cannot check for it, and the pair is
     * refused where a walk needs the direction — which is what the factories on
     * {@link CanonicalOrder} are narrow enough to be able to promise instead.
     */
    @Test
    void aDomainThatWroteItsOrderAsItsOwnComparisonIsHeldToTheSameThing() {
        CanonicalOrder<BigDecimal> asWritten = BigDecimal::compareTo;

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> asWritten.walking(
                        List.of(new BigDecimal("2.0"), new BigDecimal("2.00")),
                        Function.identity()));

        assertTrue(refused.getMessage().contains("2.0") && refused.getMessage().contains("2.00"),
                "the refusal names the two it could not tell apart: " + refused.getMessage());
    }

    /**
     * And the orders this hands out are ones whose promise can be shown.
     *
     * <p>An enum constant is equal to itself and to nothing else and compares by where it is
     * declared; a string compares as nought exactly where it is the same string. Those are the two
     * this offers, and both directions hold of each — which is what makes them safe to hand out
     * where an arbitrary comparison is not.
     */
    @Test
    void theOrdersThisHandsOutTellApartEverythingTheirDomainsDo() {
        assertEquals(List.of("a", "b"),
                CanonicalOrder.asTheyAreSpelled().walking(List.of("b", "a"), Function.identity()));
        assertEquals(List.of(Written.FIRST, Written.SECOND),
                CanonicalOrder.<Written>asTheyAreDeclared()
                        .walking(List.of(Written.SECOND, Written.FIRST), Function.identity()));
    }

    /** Two constants, to be walked in the order they are written here. */
    private enum Written {
        FIRST,
        SECOND
    }
}
