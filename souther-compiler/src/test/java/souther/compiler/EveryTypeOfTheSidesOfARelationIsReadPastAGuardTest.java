package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.test.Nightly;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static souther.compiler.AValueAGuardKeepsFromARelationIsNoValueTheRelationLeavesOpenTest.lengthGuard;
import static souther.compiler.AValueAGuardKeepsFromARelationIsNoValueTheRelationLeavesOpenTest.openAtA;
import static souther.compiler.AValueAGuardKeepsFromARelationIsNoValueTheRelationLeavesOpenTest.trimmedGuard;

/**
 * A relation leaves open none of the values a guard keeps from it, whichever types its two sides
 * are declared as: the claim of
 * {@link AValueAGuardKeepsFromARelationIsNoValueTheRelationLeavesOpenTest}, asked of every pair of
 * a declared type and a plain string for the two sides, and of the guard on the trimmed string and
 * on the length each.
 *
 * <p>Deferred to the night for what it costs: a model compiled and measured for each of eight
 * pairs and guards. No cheaper way was found to know that a side's declaration changes nothing the
 * other's does, and what it finds is as well found by the morning as by the change that caused
 * it, because the guard keeps the value from the relation before either side's declaration is
 * read.
 */
@Nightly
class EveryTypeOfTheSidesOfARelationIsReadPastAGuardTest {

    private static final List<List<String>> SIDES = List.of(
            List.of("String", "String"), List.of("T", "String"), List.of("String", "T"),
            List.of("T", "T"));

    @Test
    void theBlankStringsAGuardOnTheTrimmedStringKeepsAwayAreNotLeftOpenForAnyTypeOfTheSides() {
        for (List<String> sides : SIDES) {
            assertEquals(List.of(), openAtA(trimmedGuard(sides.get(0), sides.get(1))),
                    sides.toString());
        }
    }

    @Test
    void theShortStringsAGuardOnTheLengthKeepsAwayAreNotLeftOpenForAnyTypeOfTheSides() {
        for (List<String> sides : SIDES) {
            assertEquals(List.of(), openAtA(lengthGuard(sides.get(0), sides.get(1))),
                    sides.toString());
        }
    }
}
