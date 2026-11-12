package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.AsACompilationAllows;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Whether an element is the last to hold the value it holds is told by equality of the
 * observations only where that is the language's sameness. A key observed as a decimal at two
 * scales may be one amount, which a row does not say, so no element holding one is said to be the
 * last or not.
 */
class AnElementIsLastToHoldAValueOnlyWhereItsFormIsItsSamenessTest {

    private static final String MODEL = """
            module g

            data Row = { sku: %s, qty: Int }

            behavior decide : (rows: List<Row>) -> Int
            """;

    private static final ReadingPolicy POLICY = new ReadingPolicy(64, 12,
            AsACompilationAllows.admittedValues(), AsACompilationAllows.whatARuleLeaves());

    private static final TermPath ROWS = TermPath.of("rows");

    private static final TermPath SKU = ROWS.element().then("sku");

    private static final TypeSymbol ROW = TypeSymbols.declared(new TypeKey("g", "Row"));

    @Test
    void aKeyThatIsTextIsLastForOneElementAndNotForTheOther() {
        List<BorderQuantity.Lastness> told = lastnessOf("String",
                new ObservedValue.Text("A"), new ObservedValue.Text("A"));

        assertEquals(Set.of(new BorderQuantity.Lastness.Last(), new BorderQuantity.Lastness.NotLast()),
                Set.copyOf(told));
    }

    @Test
    void aKeyThatIsADecimalAtTwoScalesIsNotToldForEither() {
        List<BorderQuantity.Lastness> told = lastnessOf("Decimal",
                new ObservedValue.Decimal(new BigDecimal("1.0")),
                new ObservedValue.Decimal(new BigDecimal("1.00")));

        assertEquals(List.of(
                        new BorderQuantity.Lastness.CouldNotTell(ReadingGap.SAMENESS_NOT_TOLD),
                        new BorderQuantity.Lastness.CouldNotTell(ReadingGap.SAMENESS_NOT_TOLD)),
                told);
    }

    /** What stopped a key is said, and not that its sameness is not told. */
    @Test
    void aKeyThatWasNotReadInFullIsSaidAsThat() {
        ObservedValue stopped = new ObservedValue.Unknown("nothing read it");

        assertEquals(List.of(
                        new BorderQuantity.Lastness.CouldNotTell(ReadingGap.ofAComparisonOf(stopped)),
                        new BorderQuantity.Lastness.CouldNotTell(ReadingGap.ofAComparisonOf(stopped))),
                lastnessOf("Decimal", stopped, stopped));
    }

    /** The lastness of each element, each reading of a row holding one element per key asked. */
    private static List<BorderQuantity.Lastness> lastnessOf(String keyType, ObservedValue... keys) {
        Carrier whole = Carrier.ofValue(Type.Prim.INT, DeclarationAccess.NONE);
        NumericTerm.Multiplicity often = NumericTerm.Multiplicity.of(ROWS, SKU);
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        on.put(often, TermOrdersFixtures.orders(often, Carrier.TEXT, whole));
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        on.keySet().forEach(term -> coefs.put(term, ExactRatio.ONE));
        LinearQuantity quantity = new BorderQuantity.OverAForm("decide",
                new LinearForm<>(ExactRatio.ZERO, coefs), on);
        RuleReadingSource rules = RuleReadings.ofSource(MODEL.formatted(keyType));
        BehaviorInputs where = new BehaviorInputs(List.of("rows"),
                List.of(new Type.ListOf(Type.ref(ROW))), rules, POLICY);
        List<ObservedValue> rows = new ArrayList<>();
        for (int each = 0; each < keys.length; each++) {
            rows.add(new ObservedValue.Constructed(ROW, Map.of(
                    "sku", keys[each], "qty", new ObservedValue.Integer(each))));
        }
        StandingAtAPoint.Readings readings = StandingAtAPoint.readings(where,
                new ObservedInputs(List.of(new ObservedValue.Sequence(rows)),
                        new Generator.Watched.NoAccount(), new AnswerObservation.NotAnswered()),
                quantity);
        List<BorderQuantity.Lastness> out = new ArrayList<>();
        for (BorderQuantity.Observation reading : readings.tried()) {
            quantity.read(reading);
            out.add(reading.lastToHold(ROWS, SKU));
        }
        return out;
    }
}
