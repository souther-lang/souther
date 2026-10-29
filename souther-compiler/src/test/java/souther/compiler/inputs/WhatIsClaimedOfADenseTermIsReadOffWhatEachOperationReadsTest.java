package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.DecimalOperation.Formed;
import souther.compiler.inputs.DecimalOperation.Worked;
import souther.compiler.inputs.DecimalOperation.Written;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Leaves;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Operations;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Term;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Told;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BinOp;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What rows built at the ends of a run find of a decimal operation holds of every number between
 * only for what the operation reads.
 *
 * <p>Whether a decimal operation has room turns on the scale a number is written at and not on how
 * large it is: nought and 168 are worked out against a factor at the floor of the range and
 * {@code 0.5} between them is not. A row is a row where the program gets to the end of working it
 * out, so a number with no room is no row and no counterexample; what is claimed of the numbers
 * that have a row is read off the operations:
 *
 * <ul>
 * <li>an operation reading the term asked of and nothing else has room at a number or has none,
 * whichever other term is put where;
 * <li>an operation reading it with another term has room by what the other is put at, which is no
 * fact about the number, and nothing is claimed;
 * <li>an operation reading the term put beside it is worked out over numbers chosen at no more than
 * the places a row is built at, and has room for all of them or not.
 * </ul>
 */
class WhatIsClaimedOfADenseTermIsReadOffWhatEachOperationReadsTest {

    private static final NumericDomain.Bounds HOURS = new NumericDomain.Bounds(
            Endpoint.inclusive(Count.of(0)), Endpoint.inclusive(Count.of(168)));

    private static Term<String> hours(String place, long weight) {
        return new Term<>(List.of(place), ExactRatio.of(weight), HOURS, HOURS, null, true,
                Granularity.DENSE, NumericDomain.Bounds.OPEN, place);
    }

    /** {@code 4h - s >= 0}, the hours from nought to 168 on both sides. */
    private static final List<Term<String>> TERMS = List.of(hours("h", 4), hours("s", -1));

    private static final Formed H = new Formed(Map.of("h", ExactRatio.ONE), ExactRatio.ZERO);
    private static final Formed S = new Formed(Map.of("s", ExactRatio.ONE), ExactRatio.ZERO);
    private static final BigDecimal AT_THE_FLOOR = new BigDecimal(BigInteger.ONE, Integer.MAX_VALUE);

    private static DecimalOperation product(DecimalOperation.Operand one,
                                            DecimalOperation.Operand two) {
        return new DecimalOperation(BinOp.MUL, List.of(one, two), List.of());
    }

    private static DecimalOperation sum(DecimalOperation.Operand one,
                                        DecimalOperation.Operand two) {
        return new DecimalOperation(BinOp.ADD, List.of(one, two), List.of());
    }

    private static Leaves left(int asked, DecimalOperation... operations) {
        return WhatARelationLeavesUndivided.leavesOf(TERMS, asked, ExactRatio.ZERO, Rel.GE,
                String::equals, (one, other) -> true, Granularity.DENSE, null, List.of(),
                new Operations(List.of(), List.of(operations), Told.EVERY));
    }

    @Test
    void anOperationReadingOnlyTheTermAskedOfLeavesTheNumbersWithARowToBeSaidOf() {
        DecimalOperation timesFour = product(H, new Written(new BigDecimal("4.0")));
        assertInstanceOf(Leaves.Settled.class, left(0, timesFour));
    }

    @Test
    void anOperationReadingTheTermPutBesideItIsWorkedOutOverNumbersChosenAtFewPlaces() {
        DecimalOperation timesFour = product(H, new Written(new BigDecimal("4.0")));
        assertInstanceOf(Leaves.Settled.class, left(1, timesFour));
    }

    @Test
    void anOperationReadingBothTermsLeavesNothingClaimed() {
        DecimalOperation together = sum(H, S);
        assertNull(left(0, together));
        assertNull(left(1, together));
    }

    @Test
    void anOperationReadingTheTermPutBesideItAtTheFloorOfTheRangeLeavesNothingClaimed() {
        DecimalOperation atTheFloor = product(S, new Written(AT_THE_FLOOR));
        assertNull(left(0, atTheFloor));
    }

    @Test
    void anOperationWorkedOutOfBothIsReadAsBothThoughNoOperandNamesThem() {
        List<DecimalOperation> operations = List.of(product(H, new Written(BigDecimal.ONE)),
                sum(new Worked(0), S));
        assertFalse(DecimalOperation.allowAClaimOver(operations, "h", "s"));
        assertFalse(DecimalOperation.allowAClaimOver(operations, "s", "h"));
    }

    @Test
    void readsOfAnOperationAreThePlacesOfTheInputItIsWorkedOutOf() {
        List<DecimalOperation> operations = List.of(product(H, new Written(BigDecimal.ONE)),
                sum(new Worked(0), new Written(BigDecimal.TEN)), product(S, S));
        assertEquals(List.of(Set.of("h"), Set.of("h"), Set.of("s")),
                DecimalOperation.readsOf(operations));
    }

    @Test
    void aClaimIsAllowedOverNoOperationsAndOverOnesReadingNeitherTerm() {
        assertTrue(DecimalOperation.allowAClaimOver(List.of(), "h", "s"));
        assertTrue(DecimalOperation.allowAClaimOver(List.of(
                product(new Formed(Map.of("c", ExactRatio.ONE), ExactRatio.ZERO),
                        new Written(AT_THE_FLOOR))), "h", "s"));
    }

    @Test
    void aChainOfOperationsOverTheTermPutBesideItGrowsPastWhatIsShownRoomFor() {
        List<DecimalOperation> chain = new ArrayList<>();
        chain.add(product(S, S));
        for (int i = 1; i < 40_000; i++) {
            chain.add(product(new Worked(i - 1), S));
        }
        assertFalse(DecimalOperation.allowAClaimOver(chain, "h", "s"));
        assertTrue(DecimalOperation.allowAClaimOver(chain, "s", "h"));
    }
}
