package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.Extreme;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.observe.Limits;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A number of an element read off the elements beside it — how often its value occurs, the end of
 * its key's values — is read back off the container the element stands in, and not off every
 * container at that place: two orders each holding lines are two sets of lines, and a line of one
 * is no neighbour of a line of the other.
 */
class ANumberOfAnElementIsReadBackOffItsOwnContainerTest {

    private static final TermPath LINES = TermPath.of("orders").element().then("lines");

    private static final Carrier WHOLE = Carrier.ofValue(Type.Prim.INT, DeclarationAccess.NONE);

    @Test
    void theEndOfAKeysValuesIsTakenWithinOneContainer() {
        NumericTerm.ExtremeOfItsKey least = NumericTerm.ExtremeOfItsKey.of(LINES,
                LINES.element().then("sku"), LINES.element().then("qty"), Extreme.LEAST);
        TermOrders on = TermOrdersFixtures.computed(least, WHOLE, WHOLE,
                Map.of(least.keyField(), Carrier.TEXT));
        List<ObservedValue> orders = List.of(
                new ObservedValue.Sequence(List.of(line("x", 9))),
                new ObservedValue.Sequence(List.of(line("x", 2))));
        assertInstanceOf(Generator.RealizationReadback.AtRequestedPlace.class,
                Generator.readBack(on, orders, Count.of(9)),
                "the first order's least x is nine, whatever the other order holds");
    }

    @Test
    void howOftenAValueOccursIsCountedWithinOneContainer() {
        NumericTerm.Multiplicity often = NumericTerm.Multiplicity.of(LINES,
                LINES.element().then("sku"));
        TermOrders on = TermOrdersFixtures.itself(often, Carrier.TEXT);
        List<ObservedValue> orders = List.of(
                new ObservedValue.Sequence(List.of(line("x", 1))),
                new ObservedValue.Sequence(List.of(line("x", 1))));
        assertInstanceOf(Generator.RealizationReadback.Elsewhere.class,
                Generator.readBack(on, orders, Count.of(2)),
                "x occurs once in each order, and twice in none");
    }

    /**
     * A container not read whole is a reading that could not be made, never a container holding
     * nothing: an order whose lines were cut short may hold the second `x` the number asks for.
     */
    @Test
    void aContainerNotReadWholeLeavesTheNumberUntold() {
        NumericTerm.Multiplicity often = NumericTerm.Multiplicity.of(LINES,
                LINES.element().then("sku"));
        TermOrders on = TermOrdersFixtures.itself(often, Carrier.TEXT);
        List<ObservedValue> orders = List.of(
                new ObservedValue.Sequence(List.of(line("x", 1))),
                new ObservedValue.Truncated(Limits.DEFAULT.nodesFigure()));
        assertInstanceOf(Generator.ReadbackGap.Observation.class,
                assertInstanceOf(Generator.RealizationReadback.CouldNotTell.class,
                        Generator.readBack(on, orders, Count.of(2))).why());
    }

    /** And an element not read whole the same, for the end of a key's values. */
    @Test
    void anElementNotReadWholeLeavesTheEndUntold() {
        NumericTerm.ExtremeOfItsKey least = NumericTerm.ExtremeOfItsKey.of(LINES,
                LINES.element().then("sku"), LINES.element().then("qty"), Extreme.LEAST);
        TermOrders on = TermOrdersFixtures.computed(least, WHOLE, WHOLE,
                Map.of(least.keyField(), Carrier.TEXT));
        List<ObservedValue> orders = List.of(new ObservedValue.Sequence(List.of(line("x", 9),
                new ObservedValue.Truncated(Limits.DEFAULT.nodesFigure()))));
        Generator.RealizationReadback read = Generator.readBack(on, orders, Count.of(9));
        assertInstanceOf(Generator.ReadbackGap.Observation.class,
                assertInstanceOf(Generator.RealizationReadback.CouldNotTell.class, read).why(),
                "the line cut short may be an x below nine, which is the observation's to say");
    }

    /** A value read whole that holds no elements in order is no container the walk says. */
    @Test
    void aValueOfAnotherShapeIsNoContainerHoldingNothing() {
        TermOrders on = TermOrdersFixtures.itself(
                NumericTerm.Multiplicity.of(LINES, LINES.element().then("sku")), Carrier.TEXT);
        List<ObservedValue> orders = List.of(new ObservedValue.Sequence(List.of(line("x", 1))),
                new ObservedValue.Text("not lines"));
        assertEquals(new Generator.RealizationReadback.CouldNotTell(
                        new Generator.ReadbackGap.WalkAndTypeDisagree()),
                Generator.readBack(on, orders, Count.of(2)));
    }

    /** And an element read whole that holds nothing where the number is read is no element the
     *  walk says, rather than one whose number is none. */
    @Test
    void anElementOfAnotherShapeIsNoElementWithoutANumber() {
        NumericTerm.ExtremeOfItsKey least = NumericTerm.ExtremeOfItsKey.of(LINES,
                LINES.element().then("sku"), LINES.element().then("qty"), Extreme.LEAST);
        TermOrders on = TermOrdersFixtures.computed(least, WHOLE, WHOLE,
                Map.of(least.keyField(), Carrier.TEXT));
        ObservedValue noSku = new ObservedValue.Constructed(
                TypeSymbols.declared(new TypeKey("demo", "Line")),
                Map.of("qty", new ObservedValue.Integer(1)));
        List<ObservedValue> orders = List.of(new ObservedValue.Sequence(List.of(noSku)),
                new ObservedValue.Sequence(List.of(line("x", 2))));
        assertEquals(new Generator.RealizationReadback.CouldNotTell(
                        new Generator.ReadbackGap.WalkAndTypeDisagree()),
                Generator.readBack(on, orders, Count.of(9)));
    }

    private static ObservedValue line(String sku, long qty) {
        return new ObservedValue.Constructed(TypeSymbols.declared(new TypeKey("demo", "Line")),
                Map.of("sku", new ObservedValue.Text(sku), "qty", new ObservedValue.Integer(qty)));
    }
}
