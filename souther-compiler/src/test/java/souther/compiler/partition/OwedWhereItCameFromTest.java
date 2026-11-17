package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.MadeFrom;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.ValuesAt;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * What a rule about a value that came from several places is owed, and where, is read off the
 * answer of where it came from by one mapping, for the reader of a comparison and the reader of a
 * string's rule alike.
 */
class OwedWhereItCameFromTest {

    private static final TermPath A = TermPath.of("a").then("items").element();
    private static final TermPath B = TermPath.of("b").then("items").element();
    private static final TermPath C = TermPath.of("c").then("items").element();

    /**
     * A value that may stand at one of several places and came from one of several is owed at the
     * places it may stand at, with their fields, and at those it came from that they do not say.
     */
    @Test
    void aValueThatMayStandAtOneAndCameFromAnotherIsOwedAtBoth() {
        OwedWhereItCameFrom owed = OwedWhereItCameFrom.ofSeveral(
                new ValuesAt.MayStandAt(List.of(A.then("age"))),
                new MadeFrom.FromOneOf(List.of(A, B)));
        assertEquals(List.of(A.then("age"), B), owed.places());
        assertEquals(new BlockReason.RuleAboutAnElementOfSeveralContainers(), owed.why());
    }

    /** The container the name stands at an element of is the one it came from, and adds nothing. */
    @Test
    void whatItCameFromThatItStandsAtIsNotSaidTwice() {
        OwedWhereItCameFrom owed = OwedWhereItCameFrom.ofSeveral(
                new ValuesAt.MayStandAt(List.of(A.then("age"), B.then("age"))),
                new MadeFrom.FromOneOf(List.of(A, B)));
        assertEquals(List.of(A.then("age"), B.then("age")), owed.places());
    }

    /** A value that stands at one place, or at none, is read through the operation that made it,
     *  or from where it came alone. */
    @Test
    void aValueThatStandsAtNoOneOfSeveralIsLeftToTheOriginAlone() {
        assertNull(OwedWhereItCameFrom.ofSeveral(new ValuesAt.At(A), new MadeFrom.FromOneOf(
                List.of(A, B))));
        assertNull(OwedWhereItCameFrom.ofSeveral(new ValuesAt.NotAPosition(),
                new MadeFrom.FromOneOf(List.of(A, B))));
    }

    @Test
    void aValueMadeOfSeveralPlacesIsOwedTheSentenceAboutADerivedValueAtEveryOneOfThem() {
        OwedWhereItCameFrom owed = OwedWhereItCameFrom.ofSeveral(new MadeFrom.FromEvery(
                List.of(List.of(A, B), List.of(A, C))));
        assertEquals(List.of(A, B, C), owed.places());
        assertEquals(new BlockReason.RuleAboutADerivedValue(), owed.why());
    }

    @Test
    void aValueThatMayStandAtSeveralPlacesIsOwedTheSentenceAboutAnElementOfSeveralContainers() {
        OwedWhereItCameFrom owed = OwedWhereItCameFrom.ofSeveral(
                new MadeFrom.FromOneOf(List.of(A, B)));
        assertEquals(List.of(A, B), owed.places());
        assertEquals(new BlockReason.RuleAboutAnElementOfSeveralContainers(), owed.why());
    }

    @Test
    void aValueThatCameFromOnePlaceOrNoneIsLeftToTheReaderThatReadsThroughTheOperation() {
        assertNull(OwedWhereItCameFrom.ofSeveral(new MadeFrom.FromOne(A)));
        assertNull(OwedWhereItCameFrom.ofSeveral(new MadeFrom.FromNothing()));
    }
}
