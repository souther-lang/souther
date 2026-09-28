package souther.compiler.values;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Taking the one thing a collection holds is an answer about the collection, and is refused of any
 * other collection.
 *
 * <p>Said here because other things rest on it. A walk of something held in no order stops at
 * {@link TheOnly}: what comes out is the element the collection was proved to hold, so the order it
 * was walked in cannot have reached it, and a rule about where an order is read stops looking
 * there. That is a promise, and a promise nothing checks is a hole with a name
 * ({@code WhoHoldsWhatAReaderHandedOver}).
 */
class TheOneAThingHoldsIsNotTheFirstOfSeveralTest {

    @Test
    void theOneACollectionHoldsIsWhatComesBack() {
        assertEquals("only", TheOnly.of(List.of("only"), "thing"));
        assertEquals("only", TheOnly.of(Set.of("only"), "thing"));
    }

    /**
     * And a collection holding nothing is refused.
     *
     * <p>A caller here is holding a claim that failed, and what it does next rests on having the
     * thing — so the refusal is what it needs rather than an empty answer it would have to read.
     */
    @Test
    void aCollectionHoldingNothingIsRefused() {
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> TheOnly.of(List.of(), "block the positions are on"));

        assertTrue(refused.getMessage().contains("block the positions are on"),
                "the refusal says what was asked for: " + refused.getMessage());
    }

    /**
     * And so is a collection holding several, whichever of them a walk would have handed over.
     *
     * <p>The whole of what this type is for. Taking the first of several is an answer about how the
     * collection was built, and the two writings below build one collection two ways — so a reader
     * that took the first would be told two different things and this tells both of them the same
     * one.
     */
    @Test
    void aCollectionHoldingSeveralIsRefusedTheSameWayRoundOrTheOther() {
        Set<String> oneWay = new LinkedHashSet<>(List.of("b", "a"));
        Set<String> theOther = new LinkedHashSet<>(List.of("a", "b"));

        IllegalStateException first = assertThrows(IllegalStateException.class,
                () -> TheOnly.of(oneWay, "value a position is left"));
        IllegalStateException second = assertThrows(IllegalStateException.class,
                () -> TheOnly.of(theOther, "value a position is left"));

        assertEquals(first.getMessage(), second.getMessage(),
                "two writings of one collection are one collection, so what is refused of them is"
                        + " one refusal");
        assertTrue(first.getMessage().contains("a") && first.getMessage().contains("b"),
                "and it names every one of them rather than whichever came first: "
                        + first.getMessage());
    }

    /**
     * And what it hands over is not read off where anything is.
     *
     * <p>A collection of one holds the same element whichever order it is held in, which is what
     * makes taking it an answer about the collection. Said against a walk that hands its element
     * over last as readily as first.
     */
    @Test
    void whatComesBackDoesNotDependOnHowTheCollectionWasWalked() {
        List<String> backwards = new ArrayList<>(List.of("only"));

        assertEquals(TheOnly.of(backwards, "thing"),
                TheOnly.of(new LinkedHashSet<>(backwards), "thing"));
    }
}
