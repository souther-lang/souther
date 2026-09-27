package souther.compiler.meta;

import org.junit.jupiter.api.Test;
import souther.compiler.check.ConstEval;
import souther.compiler.copied.CopyRecord;
import souther.compiler.copied.CopyTarget;
import souther.compiler.execute.WrittenValue;
import souther.compiler.types.ValueName;

import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A constant is recorded as a constant exactly where its entry is a string a class file holds, and
 * that is asked without making the text of a value whose text is as long as its scale is far from
 * nought.
 */
class AConstantIsRecordedWhereItsEntryFitsAClassFileTest {

    private static final CopyTarget.Value TARGET =
            new CopyTarget.Value(new ValueName.Helper("価格", "上限"));

    /** Whether a class file can hold {@code entry} as one string: {@link DataOutputStream#writeUTF}
     *  refuses what its modified UTF-8 takes more than the constant's two bytes count. */
    private static boolean aClassFileHolds(String entry) {
        try (DataOutputStream out = new DataOutputStream(OutputStream.nullOutputStream())) {
            out.writeUTF(entry);
            return true;
        } catch (IOException tooLong) {
            return false;
        }
    }

    private static String entryOf(String content) {
        return PublishedCopies.written(Map.of(TARGET, new CopyRecord(CopyRecord.Form.CONSTANT, content)))
                .get(0);
    }

    @Test
    void theFitIsWhatTheEntryWrittenIsAsAClassFileCountsIt() {
        for (int length : new int[] {1, 100, 65_000, 65_400, 65_500, 65_510, 65_520, 65_600}) {
            String content = "0".repeat(length);
            ConstEval.Extent extent = ConstEval.extentOf(new WrittenValue.Text(content));

            assertEquals(aClassFileHolds(entryOf(new WrittenValue.Text(content).written())),
                    PublishedCopies.constantFits(TARGET, extent.chars(), extent.bytes()),
                    "a text of " + length);
        }
    }

    @Test
    void aDecimalIsMeasuredWithoutItsText() {
        BigDecimal tiny = new BigDecimal(BigInteger.ONE, 1 << 30);

        ConstEval.Extent extent = ConstEval.extentOf(new WrittenValue.Decimal(tiny));

        assertEquals((1L << 30) + 2, extent.chars());
        assertEquals(extent.chars(), extent.bytes());
        assertFalse(PublishedCopies.constantFits(TARGET, extent.chars(), extent.bytes()));
    }

    @Test
    void aDecimalOfTheLengthOfTheLastEntryThatFitsIsRecordedAndOneLongerIsNot() {
        long fits = 0;
        for (long length = 1; length < 70_000; length++) {
            if (PublishedCopies.constantFits(TARGET, length, length)) {
                fits = length;
            }
        }

        assertTrue(aClassFileHolds(entryOf("1".repeat((int) fits))));
        assertFalse(aClassFileHolds(entryOf("1".repeat((int) fits + 1))));
    }
}
