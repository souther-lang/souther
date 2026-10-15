package souther.compiler.partition;

import souther.compiler.diag.SourceRendering;
import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.GeneratedRows;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line of a form over several positions is offered a row standing on it.
 *
 * <p>A gross that is a sum of several pay fields, an allowance capped by a ceiling, and a guard
 * holding the gross against what is subtracted from it. Each of the lines the guard draws over that
 * sum is met by a row that puts the allowance at a small value, or puts several fields at large
 * values that move together, and every position of the form is unbounded above.
 *
 * <p>The claim is about the rows offered and not about what the report leaves out: a sentence the
 * report no longer says is true of a search that composed nothing as well. Each row is read back
 * as the number it adds up to, which is what a line of the form is a point of.
 */
class APositionOfAFormIsReadFromARegionHoldingTheLevelTest {

    private static final String A_CAPPED_ALLOWANCE = """
            module example.pay

            data Yen = Int
                invariant value >= 0

            data Pay =
                { base: Yen
                , scheduled: Yen
                , commuting: Yen
                , excluded: Yen
                , variable: Yen
                }

            data Over = { why: Int }
            data Amount = { v: Int }
            data Result = Over | Amount

            let total (p: Pay): Yen = p.base + p.scheduled + p.commuting + p.excluded + p.variable

            let exempt (p: Pay): Yen =
                if p.commuting > Yen(150000)
                then Yen(150000)
                else p.commuting

            behavior taxable : (pay: Pay, uplift: Yen, insurance: Yen) -> Result
                constructs Amount, Over, Yen

            let taxable (pay, uplift, insurance) = {
                let gross = total(pay) + uplift
                let subtracted = exempt(pay) + insurance
                guard gross >= subtracted else Over { why = 0 }
                Amount { v = gross.value - subtracted.value }
            }

            example taxable
                | "ordinary" :
                    (Pay { base = Yen(300000), scheduled = Yen(0), commuting = Yen(10000),
                           excluded = Yen(0), variable = Yen(0) }, Yen(0), Yen(40000))
                    -> Amount { v = 270000 }
            """;

    /** The ceiling the allowance is capped at, which is where the guard's gross - subtracted
     *  stops being the whole of the gross less the premiums. */
    private static final BigInteger CEILING = BigInteger.valueOf(150000);

    /**
     * The guard compares the gross with the exempt allowance plus the premiums. Over the fields
     * and the premiums alone, that is the sum of the fields, the uplift and the allowance, less the
     * premiums: a row is on the line of the guard's capped side where that comes to the ceiling and
     * one below it where it comes to one less.
     */
    @Test
    void theLinesOfTheSumAreEachOfferedARowThatStandsOnThem() {
        List<BigInteger> sums = sumsOfTheRowsOffered(A_CAPPED_ALLOWANCE);

        assertTrue(sums.contains(CEILING),
                () -> "a row at the line the capped side's guard is met at: " + sums);
        assertTrue(sums.contains(CEILING.subtract(BigInteger.ONE)),
                () -> "a row at the point beside it: " + sums);
        assertTrue(sums.stream().anyMatch(sum -> sum.compareTo(CEILING.subtract(BigInteger.ONE)) < 0),
                () -> "a row inside the region the line bounds: " + sums);
    }

    /**
     * Each row as {@code base + scheduled + commuting + excluded + variable + uplift - insurance},
     * in the order the rows are offered. The values are read in the order the block writes them,
     * which is the order of the model's fields and then of the behavior's parameters.
     */
    private static List<BigInteger> sumsOfTheRowsOffered(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String block = GeneratedRows.of(compilation, null, null,
                new SourceRendering(id -> "pay.sou", compilation.texts())).text();
        Pattern yen = Pattern.compile("Yen\\((\\d+)\\)");
        List<BigInteger> sums = new ArrayList<>();
        for (String row : block.split("-> <\\?>")) {
            Matcher found = yen.matcher(row);
            List<BigInteger> values = new ArrayList<>();
            while (found.find()) {
                values.add(new BigInteger(found.group(1)));
            }
            if (values.size() == 7) {
                BigInteger fields = BigInteger.ZERO;
                for (int i = 0; i < 6; i++) {
                    fields = fields.add(values.get(i));
                }
                sums.add(fields.subtract(values.get(6)));
            }
        }
        return sums;
    }
}
