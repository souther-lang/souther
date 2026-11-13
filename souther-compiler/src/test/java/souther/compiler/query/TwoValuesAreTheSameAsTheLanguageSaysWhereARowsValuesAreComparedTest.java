package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.observe.ObservedValue;
import souther.compiler.partition.BehaviorInputs;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether two values of a row are the same value is the language's to say, and a reading that
 * compares them asks it: a decimal is the amount it stands for whatever scale it was written at,
 * which the record holding one says otherwise of.
 */
class TwoValuesAreTheSameAsTheLanguageSaysWhereARowsValuesAreComparedTest {

    private static final String MODEL = """
            module probe

            data Ok = { n: Int }
            """;

    @Test
    void aDecimalIsTheSameWhateverScaleItWasWrittenAt() {
        BehaviorInputs.SameValue same = ExampleExecutions.sameValue(
                ACompiledModel.answered(MODEL).db());
        ObservedValue oneAndATenth = new ObservedValue.Decimal(new BigDecimal("1.0"));
        ObservedValue oneAndAHundredth = new ObservedValue.Decimal(new BigDecimal("1.00"));

        assertNotEquals(oneAndATenth, oneAndAHundredth,
                "as Java holds them, which is not what asks whether they are one");
        assertTrue(same.at(oneAndATenth, oneAndAHundredth, Type.Prim.DECIMAL));
        assertFalse(same.at(oneAndATenth, new ObservedValue.Decimal(new BigDecimal("1.1")),
                Type.Prim.DECIMAL));
    }

    @Test
    void aSetIsTheSameInWhateverOrderItsElementsWereMet() {
        BehaviorInputs.SameValue same = ExampleExecutions.sameValue(
                ACompiledModel.answered(MODEL).db());
        ObservedValue oneThenTwo = new ObservedValue.Sequence(List.of(
                new ObservedValue.Integer(1), new ObservedValue.Integer(2)));
        ObservedValue twoThenOne = new ObservedValue.Sequence(List.of(
                new ObservedValue.Integer(2), new ObservedValue.Integer(1)));
        Type aSet = new Type.SetOf(Type.Prim.INT);

        assertNotEquals(oneThenTwo, twoThenOne);
        assertTrue(same.at(oneThenTwo, twoThenOne, aSet));
    }
}
