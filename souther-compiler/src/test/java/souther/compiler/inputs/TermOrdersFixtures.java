package souther.compiler.inputs;

import souther.compiler.check.Carrier;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * Synthetic orders for a test that describes a term rather than reading one.
 *
 * <p>Here because a package is what package-private means, and a test source set is what says this
 * is not production. What it opens is open to tests and to nothing that ships: production reaches
 * {@link TermOrders} through {@link Quantities#ordersOf} and has no way to mint one, which is the
 * whole point of closing the constructor, and a test writing a border by hand still needs to say
 * what its number is counted on.
 */
public final class TermOrdersFixtures {

    private TermOrdersFixtures() { }

    /** A term whose value is the number it answers. */
    public static TermOrders itself(NumericTerm term, Carrier carrier) {
        return new TermOrders(term, carrier, carrier);
    }

    /** A term read on one order and answering on another, which is every taking of an operation. */
    public static TermOrders orders(NumericTerm term, Carrier observed, Carrier answered) {
        return new TermOrders(term, observed, answered);
    }

    /** A term over what a walk computed of each element, which also reads the fields it names. */
    public static TermOrders computed(NumericTerm term, Carrier observed, Carrier answered,
                                      Map<ElementProjection, Carrier> fields) {
        return computed(term, observed, answered, fields, Map.of());
    }

    /** The same, with the names the declaration puts at places of an element. */
    public static TermOrders computed(NumericTerm term, Carrier observed, Carrier answered,
                                      Map<ElementProjection, Carrier> fields,
                                      Map<ElementProjection, List<TypeSymbol>> worn) {
        return new TermOrders(term, observed, answered, fields, worn);
    }

    /**
     * What the derivation answers for a term at a type, which is the derivation itself.
     *
     * <p>For the tests that are about it: what an operation answers with, and what a value at the
     * position it was taken of is read on. Production reaches this only through a reading, which is
     * what settles which type to ask about; a test naming the type is asking the narrower question
     * of what follows from a type once one is chosen.
     */
    public static TermOrders at(NumericTerm term, Type positionType, Symbols symbols) {
        return TermOrdering.of(term, positionType, symbols, ScopedDeclarations.accessOf(symbols));
    }

    /**
     * An element read whole, as it is handed to {@code on}'s number read off its neighbours: what
     * it holds at each way into it, under the names {@code on} says are worn there, and nothing,
     * said as the way, where it holds nothing there.
     */
    public static Function<ElementProjection, TermOrders.Holding<String>> holding(
            TermOrders on, ObservedValue element) {
        return field -> on.in(field, element) instanceof ObservedValue value
                ? new TermOrders.Holding.Value<>(value)
                : new TermOrders.Holding.Nothing<>("nothing at " + field);
    }

    /** Each of {@code elements} handed over the same way. */
    public static List<Function<ElementProjection, TermOrders.Holding<String>>> holding(
            TermOrders on, List<ObservedValue> elements) {
        List<Function<ElementProjection, TermOrders.Holding<String>>> out = new ArrayList<>();
        for (ObservedValue element : elements) {
            out.add(holding(on, element));
        }
        return out;
    }

    /** The number {@code own} reads among {@code every}, put together for it alone. */
    public static TermOrders.Neighbouring<String> numberOf(TermOrders on, ObservedValue own,
                                                         List<ObservedValue> every) {
        return on.together(holding(on, every)).numberOf(holding(on, own));
    }
}
