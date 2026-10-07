package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadings;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.exact.ExactDecimals;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A value the boundary built is written the one way the language writes that value, and a value
 * that is no value — or none this can write — is said as that.
 *
 * <p>The first half is what lets two values written apart be compared by their text: a set built in
 * one order and the same set built in another are one value, and come out as one text. The second
 * half is what keeps a value from being made up where none was read.
 */
class ObservedFixturesTest {

    private static final String MODULE = """
            module example.observed

            data Point = { x: Int, y: Int }

            data Code = Int
                invariant value >= 0
            """;

    private static final RuleReadingContext READING = reading();

    @Test
    void aSetIsWrittenInTheOrderOfItsElementsTextAndAListInItsOwn() {
        ObservedValue built = new ObservedValue.Sequence(List.of(
                new ObservedValue.Integer(3), new ObservedValue.Integer(1),
                new ObservedValue.Integer(2)));
        assertEquals("[1, 2, 3]", written(built, Type.set(Type.INT)));
        assertEquals("[3, 1, 2]", written(built, Type.list(Type.INT)));
    }

    @Test
    void aMapIsWrittenInTheOrderOfItsEntriesText() {
        ObservedValue built = new ObservedValue.Mapping(List.of(
                new ObservedValue.Entry(new ObservedValue.Text("b"), new ObservedValue.Integer(2)),
                new ObservedValue.Entry(new ObservedValue.Text("a"),
                        new ObservedValue.Integer(1))));
        assertEquals("[(\"a\", 1), (\"b\", 2)]", written(built, Type.map(Type.STRING, Type.INT)));
    }

    /** At its fewest digits, and as a decimal wherever the position is one — a boundary carries
     *  a whole number there. */
    @Test
    void aDecimalIsWrittenAtItsFewestDigitsAndAsWhatThePositionDeclares() {
        assertEquals("1.5m", written(new ObservedValue.Decimal(new BigDecimal("1.50")),
                Type.DECIMAL));
        assertEquals("2m", written(new ObservedValue.Integer(2), Type.DECIMAL));
    }

    @Test
    void aRecordIsWrittenInTheOrderItsDeclarationWritesItsFields() {
        ObservedValue built = new ObservedValue.Constructed(declared("Point"),
                Map.of("y", new ObservedValue.Integer(2), "x", new ObservedValue.Integer(1)));
        assertEquals("Point { x = 1, y = 2 }", written(built, Type.ref(declared("Point"))));
    }

    @Test
    void aNewtypeIsWrittenUnderItsName() {
        ObservedValue built = new ObservedValue.Constructed(declared("Code"),
                Map.of("value", new ObservedValue.Integer(3)));
        assertEquals("Code(3)", written(built, Type.ref(declared("Code"))));
    }

    /** What could not be read back and what a limit stopped are no value, wherever they stand. */
    @Test
    void aValueNothingReadIsNotWritten() {
        notWritable(new ObservedValue.Unknown("unreadable"), Type.INT);
        notWritable(new ObservedValue.Truncated(), Type.list(Type.INT));
        notWritable(new ObservedValue.Constructed(declared("Point"),
                Map.of("x", new ObservedValue.Integer(1), "y", new ObservedValue.Truncated())),
                Type.ref(declared("Point")));
    }

    /**
     * A value that is not the construction the position declares is not written as either — and
     * the position does not make up what the value lacks: a name it never wore, the temporal it
     * was not, a field the declaration has no place for.
     */
    @Test
    void aValueOfAnotherShapeIsNotWritten() {
        notWritable(new ObservedValue.Text("7"), Type.INT);
        notWritable(new ObservedValue.Constructed(declared("Code"),
                Map.of("value", new ObservedValue.Integer(3))), Type.ref(declared("Point")));
        notWritable(new ObservedValue.Integer(3), Type.ref(declared("Code")));
        notWritable(new ObservedValue.Temporal("2024-02-29"), Type.Prim.TIME);
        notWritable(new ObservedValue.Constructed(declared("Point"),
                Map.of("x", new ObservedValue.Integer(1), "y", new ObservedValue.Integer(2),
                        "z", new ObservedValue.Integer(3))), Type.ref(declared("Point")));
    }

    /** A temporal is written as the one its text is, where that is the one the position is. */
    @Test
    void aTemporalIsWrittenAsTheOneItIs() {
        assertEquals("Date(\"2024-02-29\")",
                written(new ObservedValue.Temporal("2024-02-29"), Type.Prim.DATE));
    }

    /** A decimal the grammar has no plain literal for. */
    @Test
    void aDecimalWithNoLiteralIsNotWritten() {
        notWritable(new ObservedValue.Decimal(
                BigDecimal.ONE.scaleByPowerOfTen(ExactDecimals.MAX_SPELT_OUT_DIGITS + 1)),
                Type.DECIMAL);
    }

    private static String written(ObservedValue value, Type type) {
        return assertInstanceOf(ObservedFixtures.Writing.Written.class,
                ObservedFixtures.of(value, type, READING),
                () -> "written: " + value).value() instanceof FixtureTemplate fixture
                ? fixture.text() : null;
    }

    private static void notWritable(ObservedValue value, Type type) {
        assertInstanceOf(ObservedFixtures.Writing.NotWritable.class,
                ObservedFixtures.of(value, type, READING), () -> "not written: " + value);
    }

    private static TypeSymbol declared(String name) {
        return TypeSymbols.declared(new TypeKey("example.observed", name));
    }

    private static RuleReadingContext reading() {
        Compilation compilation = Compilation.ofSource(MODULE, "Main");
        compilation.answerEverything();
        return RuleReadingContext.unshared(
                RuleReadings.of(compilation, compilation.modules().get(0)),
                ReadAs.THE_COMPILATION_DOES);
    }
}
