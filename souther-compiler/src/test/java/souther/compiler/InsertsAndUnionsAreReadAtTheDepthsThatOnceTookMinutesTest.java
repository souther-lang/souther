package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.test.Nightly;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.AGuardThatAValueIsNotInASetIsReadByWhatAnInsertOfItAnswersTest.aChainOfInserts;
import static souther.compiler.AGuardThatAValueIsNotInASetIsReadByWhatAnInsertOfItAnswersTest.aSetUnitedWithItself;
import static souther.compiler.AGuardThatAValueIsNotInASetIsReadByWhatAnInsertOfItAnswersTest.insertsOnBothSides;
import static souther.compiler.AGuardThatAValueIsNotInASetIsReadByWhatAnInsertOfItAnswersTest.warnings;

/**
 * The programs of {@link AGuardThatAValueIsNotInASetIsReadByWhatAnInsertOfItAnswersTest} that hold
 * how an insert or a union is read to growing with the depth, read at the depths a long chain of
 * them has: what they say is what they say at the least depth that has the shape.
 *
 * <p>Left to the nightly because of what it costs: a few seconds a program at these depths, where
 * the shape itself is held on every change by how many premises are looked at
 * ({@code assertGrowsNoFasterThanTheCube}) and not by how long a run takes. What this finds is as
 * well found by the morning as by the change that caused it — a depth at which a read stops
 * finishing, or says another thing than it does at four.
 */
@Nightly
class InsertsAndUnionsAreReadAtTheDepthsThatOnceTookMinutesTest {

    @Test
    void manyInsertsOnBothSidesAreReadAtTheDepthOfALongChain() {
        assertEquals(List.of("E2011"), warnings(insertsOnBothSides(24)));
    }

    @Test
    void aChainOfInsertsIsReadAtTheDepthOfALongChain() {
        assertEquals(List.of(), warnings(aChainOfInserts(16)));
    }

    /** Held at the depth where it says nothing, and read to the end at the depth where it says what
     *  the rounds could not settle, which is what it said before as well. */
    @Test
    void aSetUnitedWithItselfIsReadAtTheDepthOfALongChain() {
        assertEquals(List.of(), warnings(aSetUnitedWithItself(16)));
        List<String> deeper = warnings(aSetUnitedWithItself(24));
        assertTrue(List.of(List.<String>of(), List.of("E2011")).contains(deeper),
                "a set united with itself 24 times said " + deeper);
    }
}
