package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Towards;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An item holding one number of a quantity taken of several positions is not one number of any of
 * them.
 *
 * <p>Where the quantity is one position's own values, what the item leaves it is what it leaves
 * that position, and a search that tried the number the item names has tried every number the item
 * asks for. Where the quantity is taken of several — how far two stand apart, what a form of them
 * comes to — the same item leaves each of them every number the others leave room for: a distance
 * of exactly ten is the near position anywhere the far one is ten away. A search that tried one such
 * pair tried the pair the solver picked.
 *
 * <p>So the item travels whole rather than being written down against each position, and what it
 * says about any one of them is that the walk of that one was not the walk of the question.
 */
class OneNumberOfADerivedQuantityIsNotOneNumberOfItsPositionsTest {

    private static NumericTerm.FromOnePosition value(String field) {
        return new NumericTerm.ValueOf(TermPath.of("p").then(field));
    }

    private static TermOrders on(String field) {
        return TermOrdersFixtures.itself(value(field), Carrier.WHOLE);
    }

    private static Level at(long value) {
        return new Level.OnACarrier(Carrier.WHOLE, Count.of(value));
    }

    /** The run from one value to another, both ends held. */
    private static Band between(long low, long high) {
        return new Band(Band.endAt(null, Bound.at(at(low), true), Towards.ABOVE),
                Band.endAt(null, Bound.at(at(high), true), Towards.BELOW));
    }

    private static final BorderQuantity ONE_POSITION =
            new BorderQuantity.OfACoordinate("take", value("n"), on("n"));

    private static final BorderQuantity HOW_FAR_APART =
            new BorderQuantity.Apart("take", on("n"), on("m"));

    private static final BorderQuantity WHAT_A_FORM_COMES_TO = new BorderQuantity.OverAForm("take",
            new LinearForm<>(BigDecimal.ZERO,
                    Map.of(value("n"), BigDecimal.ONE, value("m"), BigDecimal.ONE)),
            Map.of(value("n"), on("n"), value("m"), on("m")));

    /** An item at one level of the quantity, which is one number of it. */
    private static final Criterion AT_ONE_LEVEL = new Criterion.AtTheLevel(at(10));

    /** An item that is a run of the quantity with one value of it taken out. */
    private static final Criterion IN_A_RUN_BUT_ONE =
            new Criterion.Within(between(0, 20), at(10), Towards.ABOVE);

    /** One position's own values are what the item leaves that position, one number and all. */
    @Test
    void anItemOfOnePositionsValuesIsThatPositionsQuestion() {
        NumbersAskedFor asked = ONE_POSITION.asksOfEachTerm(AT_ONE_LEVEL);

        assertTrue(asked.isOneNumber(),
                "an item at one level of a position's own values asks for that one number");
        assertTrue(asked.values().contains(at(10)), "which is the number the item names");
        assertFalse(asked.values().contains(at(9)), "and nothing beside it");
    }

    /** A distance of exactly one number leaves each position every number the other leaves. */
    @Test
    void oneDistanceIsNotOneNumberOfEitherPosition() {
        NumbersAskedFor asked = HOW_FAR_APART.asksOfEachTerm(AT_ONE_LEVEL);

        assertFalse(asked.isOneNumber(),
                "a pair standing one distance apart stands at many pairs of numbers");
        assertFalse(asked.isWalkedWhole(),
                "so walking one position's order is not walking what was asked");
        assertTrue(asked.values().contains(at(0)), "and nothing of either order is taken away");
        assertTrue(asked.values().contains(at(10)), "at the item's own number or away from it");
    }

    /** And a form coming to exactly one number is the same statement about its positions. */
    @Test
    void oneNumberOfAFormIsNotOneNumberOfItsPositions() {
        NumbersAskedFor asked = WHAT_A_FORM_COMES_TO.asksOfEachTerm(AT_ONE_LEVEL);

        assertFalse(asked.isOneNumber(),
                "a form at one level is every pair of numbers that comes to it");
        assertFalse(asked.isWalkedWhole(), "so neither position was walked whole");
        assertTrue(asked.values().contains(at(10)),
                "and what the form says leaves each position its order");
    }

    /** The item travels as the item, which is the quantity standing where the criterion says. */
    @Test
    void whatIsCarriedIsTheQuantityStandingWhereTheItemSays() {
        NumbersAskedFor asked = WHAT_A_FORM_COMES_TO.asksOfEachTerm(AT_ONE_LEVEL);

        assertEquals(List.of(new QuantityInRegion(WHAT_A_FORM_COMES_TO, AT_ONE_LEVEL.region())),
                asked.onlyTogether(),
                "the quantity and where it stands, in the words the item is already written in");
        assertEquals(java.util.Set.of(value("n"), value("m")),
                asked.onlyTogether().getFirst().terms(),
                "and it is about both of the positions it is taken of");
    }

    /**
     * A value the item is away from stays out of it when it travels.
     *
     * <p>An item is a run less the value against the line, and that is what a row's number has to
     * be in. Written out as a pair of ends on the way through, the row would be offered standing
     * on the line the item is named for being beside.
     */
    @Test
    void anItemAValueIsTakenOutOfKeepsTheHoleAsItTravels() {
        NumbersAskedFor asked = WHAT_A_FORM_COMES_TO.asksOfEachTerm(IN_A_RUN_BUT_ONE);
        LevelRegion values = ((QuantityInRegion) asked.onlyTogether().getFirst()).values();

        assertTrue(values.contains(at(9)), "what lies under the value taken out is in the item");
        assertTrue(values.contains(at(11)), "and what lies over it");
        assertFalse(values.contains(at(10)), "and the value against the line is not");
        assertFalse(values.contains(at(21)), "with the run's own ends holding");
    }

    /** The same item of one position's own values keeps the hole in the term's own question. */
    @Test
    void aPositionsOwnItemKeepsItsHoleWhereItIsAsked() {
        NumbersAskedFor asked = ONE_POSITION.asksOfEachTerm(IN_A_RUN_BUT_ONE);

        assertTrue(asked.isWalkedWhole(), "a position's own item is a set of its own");
        assertTrue(asked.values().contains(at(9)), "holding what lies under the value taken out");
        assertFalse(asked.values().contains(at(10)), "and not the value against the line");
        assertFalse(asked.isOneNumber(), "which is a class of numbers and not one of them");
    }
}
