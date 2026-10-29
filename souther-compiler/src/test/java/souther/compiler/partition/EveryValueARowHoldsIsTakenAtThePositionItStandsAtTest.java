package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A value a row holds is known at the position it stood at, wherever in the row that was: in a list,
 * in a field of a record, in a record in a list, behind a name a type wears, in a case of a sum.
 *
 * <p>What a search grows a list from is what the rows ran a position of the element's type with, so
 * a value that is only ever met inside a record is a value the search never reuses unless it is taken
 * at the position inside.
 */
class EveryValueARowHoldsIsTakenAtThePositionItStandsAtTest {

    private static final String MODULE = """
            module example.taken

            data Point = { x: Int, y: Int }

            data Code = Int
                invariant value >= 0

            data Basket = { items: List<Int>, code: Code, points: List<Point> }

            data Dot
            data Bar = { length: Int }
            data Mark = Dot | Bar
            """;

    private static ObservedValue whole(long n) {
        return new ObservedValue.Integer(n);
    }

    private static ObservedValue listOf(ObservedValue... elements) {
        return new ObservedValue.Sequence(List.of(elements));
    }

    private static TypeSymbol declared(String name) {
        return TypeSymbols.declared(new TypeKey("example.taken", name));
    }

    private static ObservedValue point(long x, long y) {
        return new ObservedValue.Constructed(declared("Point"),
                Map.of("x", whole(x), "y", whole(y)));
    }

    private static List<InputsRowsRanWith.Taken> takenAt(Type type, ObservedValue value) {
        Compilation compilation = Compilation.ofSource(MODULE, "Main");
        RuleReadingSource source = Shapes.ruleReading(compilation.db(), "example.taken").value();
        assertNotNull(source, "the model under test compiles");
        List<InputsRowsRanWith.Taken> out = new ArrayList<>();
        InputsRowsRanWith.takenAt(type, value, source, out);
        return out;
    }

    private static Set<ObservedValue> valuesAt(List<InputsRowsRanWith.Taken> taken, Type type) {
        return taken.stream().filter(each -> each.type().equals(type))
                .map(InputsRowsRanWith.Taken::value).collect(Collectors.toSet());
    }

    /** A list gives each element at the element's type, at every depth. */
    @Test
    void anElementOfAListIsTakenAtTheElementsType() {
        ObservedValue first = listOf(whole(103));
        ObservedValue second = listOf(whole(107), whole(109));

        List<InputsRowsRanWith.Taken> taken =
                takenAt(Type.list(Type.list(Type.INT)), listOf(first, second));

        assertEquals(Set.of(whole(103), whole(107), whole(109)), valuesAt(taken, Type.INT));
        assertEquals(Set.of(first, second), valuesAt(taken, Type.list(Type.INT)));
    }

    /** The fields of a record, and the elements of the lists they hold. */
    @Test
    void whatARecordHoldsIsTakenAtTheTypesOfItsFields() {
        ObservedValue basket = new ObservedValue.Constructed(declared("Basket"), Map.of(
                "items", listOf(whole(103), whole(107)),
                "code", new ObservedValue.Constructed(declared("Code"), Map.of("value", whole(5))),
                "points", listOf(point(1, 2), point(3, 4))));

        List<InputsRowsRanWith.Taken> taken = takenAt(Type.ref(declared("Basket")), basket);

        assertEquals(Set.of(whole(103), whole(107), whole(1), whole(2), whole(3), whole(4)),
                valuesAt(taken, Type.INT));
        assertEquals(Set.of(point(1, 2), point(3, 4)),
                valuesAt(taken, Type.ref(declared("Point"))));
        assertEquals(Set.of(basket), valuesAt(taken, Type.ref(declared("Basket"))));
    }

    /** The case of a sum is taken as the case it is. */
    @Test
    void theCaseASumIsIsTakenWithWhatItHolds() {
        ObservedValue bar = new ObservedValue.Constructed(declared("Bar"),
                Map.of("length", whole(7)));

        List<InputsRowsRanWith.Taken> taken = takenAt(Type.ref(declared("Mark")), bar);

        assertEquals(Set.of(whole(7)), valuesAt(taken, Type.INT));
        assertEquals(Set.of(bar), valuesAt(taken, Type.ref(declared("Bar"))));
    }

    /** What was not read holds nothing to take, and is kept as it was met. */
    @Test
    void aValueNothingWasReadOfHoldsNothingToTake() {
        ObservedValue unread = new ObservedValue.Unknown("not read");

        List<InputsRowsRanWith.Taken> taken = takenAt(Type.list(Type.INT), unread);

        assertEquals(List.of(new InputsRowsRanWith.Taken(Type.list(Type.INT), unread)), taken);
    }
}
