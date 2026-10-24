package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadings;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The values one step from a value are those with one whole number moved by one, the number being
 * what the position's type says is one.
 *
 * <p>Read through the type and not through the value: a boundary carries a whole number where a
 * {@code Decimal} stands, and the value alone cannot tell that from an {@code Int}.
 */
class NearbyValuesTest {

    private static final String MODULE = """
            module example.nearby

            data Point = { x: Int, y: Int }

            data Code = Int
                invariant value >= 0

            data Priced = { code: Code, price: Decimal }
            """;

    private static final RuleReadingContext READING = reading();

    private static ObservedValue whole(long n) {
        return new ObservedValue.Integer(n);
    }

    private static List<ObservedValue> all(ObservedValue value, Type type) {
        List<ObservedValue> out = new ArrayList<>();
        NearbyValues.of(value, type, READING).forEachRemaining(out::add);
        return out;
    }

    private static ObservedValue point(long x, long y) {
        return new ObservedValue.Constructed(declared("Point"), Map.of("x", whole(x), "y", whole(y)));
    }

    @Test
    void aWholeNumberHasOneMoreAndOneLess() {
        assertEquals(List.of(whole(6), whole(4)), all(whole(5), Type.INT));
    }

    /** Nothing past the ends: a step that overflows is no neighbour. */
    @Test
    void theEndsOfTheRangeHaveOneNeighbour() {
        assertEquals(List.of(whole(Long.MAX_VALUE - 1)), all(whole(Long.MAX_VALUE), Type.INT));
        assertEquals(List.of(whole(Long.MIN_VALUE + 1)), all(whole(Long.MIN_VALUE), Type.INT));
    }

    /** One number at a time, the rest as it was, in the order the declaration writes the fields. */
    @Test
    void aRecordMovesOneFieldPerCandidate() {
        assertEquals(List.of(point(2, 7), point(0, 7), point(1, 8), point(1, 6)),
                all(point(1, 7), Type.ref(declared("Point"))));
    }

    @Test
    void aListMovesOneElementPerCandidate() {
        ObservedValue held = new ObservedValue.Sequence(List.of(whole(1), whole(10)));
        assertEquals(List.of(
                        new ObservedValue.Sequence(List.of(whole(2), whole(10))),
                        new ObservedValue.Sequence(List.of(whole(0), whole(10))),
                        new ObservedValue.Sequence(List.of(whole(1), whole(11))),
                        new ObservedValue.Sequence(List.of(whole(1), whole(9)))),
                all(held, Type.list(Type.INT)));
    }

    /** The name the position wears goes back on what was moved. */
    @Test
    void aNewtypeKeepsItsNameAroundTheNumber() {
        ObservedValue code = new ObservedValue.Constructed(declared("Code"),
                Map.of("value", whole(3)));
        assertEquals(List.of(
                        new ObservedValue.Constructed(declared("Code"), Map.of("value", whole(4))),
                        new ObservedValue.Constructed(declared("Code"), Map.of("value", whole(2)))),
                all(code, Type.ref(declared("Code"))));
    }

    /**
     * A whole number standing at a {@code Decimal} is a decimal, and a decimal has nothing directly
     * beside it. The number beside it in the same record is still moved.
     */
    @Test
    void aWholeNumberAtADecimalIsNotMoved() {
        ObservedValue priced = new ObservedValue.Constructed(declared("Priced"), Map.of(
                "code", new ObservedValue.Constructed(declared("Code"), Map.of("value", whole(3))),
                "price", whole(10)));

        List<ObservedValue> near = all(priced, Type.ref(declared("Priced")));

        assertEquals(2, near.size(), "the code's two neighbours and none for the price");
        for (ObservedValue each : near) {
            assertEquals(whole(10), ((ObservedValue.Constructed) each).field("price"));
        }
        assertEquals(List.of(), all(whole(10), Type.DECIMAL));
    }

    @Test
    void whatIsNotANumberHasNoNeighbour() {
        assertEquals(List.of(), all(new ObservedValue.Text("a"), Type.STRING));
        assertEquals(List.of(), all(new ObservedValue.Bool(true), Type.BOOL));
        assertEquals(List.of(), all(new ObservedValue.Unknown("unreadable"), Type.INT));
    }

    /**
     * Made when asked for. A list of many numbers has as many candidates as it has numbers twice,
     * and a search that takes a few leaves the rest unmade.
     */
    @Test
    void aCandidateIsMadeOnlyWhenAsked() {
        List<ObservedValue> elements = new ArrayList<>();
        for (int i = 0; i < 1000; i++) {
            elements.add(whole(i));
        }
        Iterator<ObservedValue> near = NearbyValues.of(new ObservedValue.Sequence(elements),
                Type.list(Type.INT), READING);

        ObservedValue.Sequence first = (ObservedValue.Sequence) near.next();

        assertEquals(whole(1), first.elements().get(0));
        assertEquals(1000, first.elements().size());
        assertTrue(near.hasNext(), "the rest are still to come");
    }

    private static TypeSymbol declared(String name) {
        return TypeSymbols.declared(new TypeKey("example.nearby", name));
    }

    private static RuleReadingContext reading() {
        Compilation compilation = Compilation.ofSource(MODULE, "Main");
        return RuleReadingContext.unshared(
                RuleReadings.of(compilation, compilation.modules().get(0)),
                ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
    }
}
