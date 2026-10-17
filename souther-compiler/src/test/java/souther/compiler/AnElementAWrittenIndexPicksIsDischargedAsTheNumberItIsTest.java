package souther.compiler;

import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a rule is discharged, the name a {@code Some} arm opens over {@code List.get(i, xs)} is the
 * number written at {@code i}, where {@code i} is written down and {@code xs} is a list written out
 * or the code points of a text written down.
 *
 * <p>Both directions: under {@code c >= 48}, {@code c - zero} is at or above nought where the
 * element is forty-eight and may be below it where the element is forty-nine. That the measure
 * reads the same element is {@link WhereAWrittenValueIsReadTheMeasureAndTheDischargeAgreeTest}'s.
 */
class AnElementAWrittenIndexPicksIsDischargedAsTheNumberItIsTest {

    private static boolean owed(String picked) {
        String source = """
                module demo

                data Digit = Int
                    invariant atLeastNought = value >= 0

                let zeroText = "0"

                let digitValue (c: Int, xs: List<Int>): Int =
                    match %s with
                        | Some zero -> c - zero
                        | None -> 0

                behavior f : (c: Int, xs: List<Int>) -> Digit
                    constructs Digit
                let f (c, xs) = if c >= 48 then Digit(digitValue(c, xs)) else Digit(0)
                """.formatted(picked);
        return Compiler.compileWithWarnings(source).warnings().stream()
                .anyMatch(d -> d.severity() == Severity.WARNING && "E2011".equals(d.code()));
    }

    @Test
    void aCodePointAboveTheGuardIsOwed() {
        assertTrue(owed("List.get(0, String.codePoints(\"1\"))"),
                "the code point of \"1\" is forty-nine, and c may be forty-eight");
    }

    @Test
    void anElementOfAListWrittenOutIsTheNumberTheArmNames() {
        assertFalse(owed("List.get(1, [49, 48])"), "the element at one is forty-eight");
        assertTrue(owed("List.get(0, [49, 48])"), "and the element at nought is forty-nine");
    }

    @Test
    void aTextAndAnIndexReachedThroughNamesArePickedTheSameWay() {
        assertFalse(owed("""
                {
                        let codes = String.codePoints(zeroText)
                        let first = 0
                        List.get(first, codes)
                    }"""), "the names are followed to what they were given");
    }
}
