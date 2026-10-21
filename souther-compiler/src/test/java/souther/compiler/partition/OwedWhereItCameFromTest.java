package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.TermPath;

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

    @Test
    void aValueMadeOfSeveralPlacesIsOwedTheSentenceAboutADerivedValueAtEveryOneOfThem() {
        OwedWhereItCameFrom owed = OwedWhereItCameFrom.ofSeveral(new PathResolution.MadeOf(
                List.of(List.of(A, B), List.of(A, C))));
        assertEquals(List.of(A, B, C), owed.places());
        assertEquals(new BlockReason.RuleAboutADerivedValue(), owed.why());
    }

    @Test
    void aValueThatMayStandAtSeveralPlacesIsOwedTheSentenceAboutAnElementOfSeveralContainers() {
        OwedWhereItCameFrom owed = OwedWhereItCameFrom.ofSeveral(
                new PathResolution.MayStandAt(List.of(A, B)));
        assertEquals(List.of(A, B), owed.places());
        assertEquals(new BlockReason.RuleAboutAnElementOfSeveralContainers(), owed.why());
    }

    @Test
    void aValueThatCameFromOnePlaceOrNoneIsLeftToTheReaderThatReadsThroughTheOperation() {
        assertNull(OwedWhereItCameFrom.ofSeveral(new PathResolution.At(A)));
        assertNull(OwedWhereItCameFrom.ofSeveral(new PathResolution.NotAPosition()));
    }
}
