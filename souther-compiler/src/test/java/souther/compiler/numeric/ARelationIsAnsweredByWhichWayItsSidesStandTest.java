package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.NumericDomain.Rel;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a relation says at a value, and what its denial says there.
 *
 * <p>The two things every reader of a relation asks, answered here so that they are answered once.
 * Both are written out as data: a table derived from the rule it is holding would agree with that
 * rule however the rule read the difference, and which way the difference is read is the one thing
 * about this that a reader can get wrong without anything else showing it.
 *
 * <p>Three values of the difference and no more, because a relation is a question about which way
 * the sides stand and there are three ways.
 */
class ARelationIsAnsweredByWhichWayItsSidesStandTest {

    /** A relation, a way the left side stands to the right, and whether it holds there. */
    private record Row(Rel rel, int sign, boolean holds) {

        String asked() {
            return rel + " where the left stands " + (sign < 0 ? "below" : sign > 0 ? "above" : "at")
                    + " the right";
        }
    }

    private static Row row(Rel rel, int sign, boolean holds) {
        return new Row(rel, sign, holds);
    }

    private static final List<Row> ROWS = List.of(
            row(Rel.GE, -1, false), row(Rel.GE, 0, true), row(Rel.GE, 1, true),
            row(Rel.GT, -1, false), row(Rel.GT, 0, false), row(Rel.GT, 1, true),
            row(Rel.LE, -1, true), row(Rel.LE, 0, true), row(Rel.LE, 1, false),
            row(Rel.LT, -1, true), row(Rel.LT, 0, false), row(Rel.LT, 1, false),
            row(Rel.EQ, -1, false), row(Rel.EQ, 0, true), row(Rel.EQ, 1, false),
            row(Rel.NE, -1, true), row(Rel.NE, 0, false), row(Rel.NE, 1, true));

    /** What each relation is denied by, written out for the same reason the table above is. */
    private static final List<String> DENIALS = List.of(
            "GE denied is LT", "GT denied is LE", "LE denied is GT",
            "LT denied is GE", "EQ denied is NE", "NE denied is EQ");

    @Test
    void whichWayTheSidesStandDecidesWhetherARelationHolds() {
        List<String> expected = new ArrayList<>();
        ROWS.forEach(each -> expected.add(each.asked() + ": " + each.holds()));

        List<String> answered = new ArrayList<>();
        ROWS.forEach(each -> answered.add(each.asked() + ": " + each.rel().holds(each.sign())));

        assertEquals(expected, answered);
    }

    @Test
    void aRelationIsDeniedByTheOneThatHoldsWhereItDoesNot() {
        List<String> answered = new ArrayList<>();
        for (Rel rel : Rel.values()) {
            answered.add(rel + " denied is " + rel.denied());
        }

        assertEquals(DENIALS, answered);
    }

    /**
     * And the denial is the denial at every value, which is what makes the table above a rule about
     * the relation rather than a naming of pairs.
     */
    @Test
    void whatIsDeniedHoldsExactlyWhereTheRelationDoesNot() {
        List<String> disagreeing = new ArrayList<>();
        for (Rel rel : Rel.values()) {
            for (int sign = -1; sign <= 1; sign++) {
                if (rel.denied().holds(sign) == rel.holds(sign)) {
                    disagreeing.add(rel + " and " + rel.denied() + " agree at " + sign);
                }
            }
        }

        assertEquals(List.of(), disagreeing);
    }

    /**
     * Every relation there is, so that one added later is one this was asked about.
     *
     * <p>A table written out says nothing about what it left out. Held against the relations
     * themselves, a seventh is a failure here rather than a value two of the readings answer
     * differently.
     */
    @Test
    void everyRelationIsAnsweredFor() {
        Set<Rel> asked = EnumSet.noneOf(Rel.class);
        ROWS.forEach(each -> asked.add(each.rel()));

        assertEquals(EnumSet.allOf(Rel.class), asked);
        assertEquals(Rel.values().length, DENIALS.size());
        // Each of them at each of the three ways the sides can stand. The table above is what both
        // halves of the first test are read out of, so a row taken out of it goes from both and
        // nothing else would say so.
        assertEquals(Rel.values().length * 3, ROWS.size(),
                "every relation at each of the three ways the two sides can stand");
    }
}
