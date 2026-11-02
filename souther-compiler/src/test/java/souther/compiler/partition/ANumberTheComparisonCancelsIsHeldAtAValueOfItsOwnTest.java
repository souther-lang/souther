package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A number the comparison cancels out of the form is still worked out by the program, and a row
 * that holds it large stops there. The relation is shown to reach every value of its sides where
 * the cancelled number can be held at a value of its own, one the declarations leave it nearest
 * nought, and a row is built at it.
 *
 * <p>In {@code base + commuting >= commuting + social} the relation is {@code base >= social}
 * and {@code commuting} is no side of it, but {@code base + commuting} and
 * {@code commuting + social} are worked out all the same.
 *
 * <p>What is shown is that rows exist, at the held value. Rows where the number stands elsewhere
 * are not said to be none: the number held at nought leaves {@code x} of 100 no computed row in
 * {@code x + c + MAX - MAX >= c + y}, which a row at {@code c} of -100 has.
 */
class ANumberTheComparisonCancelsIsHeldAtAValueOfItsOwnTest {

    private static final BigInteger GREATEST = BigInteger.valueOf(Long.MAX_VALUE);
    private static final BigInteger LEAST = BigInteger.valueOf(Long.MIN_VALUE);

    private static Compilation measuredSource(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static Compilation measured(String commutingRule, String comparison) {
        return measuredSource("""
                module demo

                data Yen = Int
                    invariant value >= 0

                data M = { base: Yen, commuting: Yen, other: Yen }
                    invariant base.value >= 0
                    %s

                behavior f : (m: M, social: Int) -> Bool
                let f (m, social) = %s
                """.formatted(commutingRule, comparison));
    }

    private static final String CANCELLED =
            "m.base.value + m.commuting.value >= m.commuting.value + social";

    private static boolean notShown(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE))
                .contains("relation_not_shown_to_reach_every_value");
    }

    private static String offered(Compilation compilation) {
        return GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule("demo")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()), compilation.db())
                .text();
    }

    /** One row offered: the values of {@code base}, {@code commuting} and {@code social}. */
    private record Row(BigInteger base, BigInteger commuting, BigInteger social) {

        /** Whether the program works out every operation of the row inside an {@code Int}. */
        boolean getsPast() {
            return within(base.add(commuting)) && within(commuting.add(social));
        }

        boolean holds() {
            return base.add(commuting).compareTo(commuting.add(social)) >= 0;
        }

        private static boolean within(BigInteger value) {
            return value.compareTo(LEAST) >= 0 && value.compareTo(GREATEST) <= 0;
        }
    }

    private static List<Row> rowsOffered(Compilation compilation) {
        List<Row> out = new ArrayList<>();
        Matcher row = Pattern.compile("base = Yen\\((-?\\d+)\\), commuting = Yen\\((-?\\d+)\\),"
                + " other = Yen\\(-?\\d+\\) \\}, (-?\\d+)\\)").matcher(offered(compilation));
        while (row.find()) {
            out.add(new Row(new BigInteger(row.group(1)), new BigInteger(row.group(2)),
                    new BigInteger(row.group(3))));
        }
        return out;
    }

    @Test
    void theRelationIsShownWhereTheCancelledNumberIsHeldAtNought() {
        Compilation compilation = measured("invariant commuting.value >= 0", CANCELLED);

        assertFalse(notShown(compilation), () -> offered(compilation));
    }

    @Test
    void aRowIsBuiltOnEachSideOfTheLineWithTheNumberAtTheValueHeldForIt() {
        Compilation compilation = measured("invariant commuting.value >= 5", CANCELLED);
        List<Row> rows = rowsOffered(compilation);

        BigInteger held = BigInteger.valueOf(5);
        assertTrue(rows.stream().anyMatch(row -> row.holds() && row.commuting().equals(held)),
                () -> "a row where it holds, the number at the value held for it: " + rows);
        assertTrue(rows.stream().anyMatch(row -> !row.holds() && row.commuting().equals(held)),
                () -> "a row where it fails, the number at the value held for it: " + rows);
        assertTrue(rows.stream().allMatch(Row::getsPast),
                () -> "every operation of every row is worked out: " + rows);
    }

    @Test
    void aNumberTiedToASideByARuleIsNotHeldApart() {
        Compilation compilation = measured("invariant commuting.value == base.value", CANCELLED);

        assertTrue(notShown(compilation), () -> offered(compilation));
    }

    @Test
    void aNumberTheDeclarationsLeaveNoValueNearNoughtIsNotHeldWhereTheOperationsStop() {
        Compilation compilation = measured(
                "invariant commuting.value >= 9223372036854775807", CANCELLED);

        assertTrue(notShown(compilation), () -> offered(compilation));
    }

    /**
     * Held at nought, {@code c} leaves {@code x} of 100 no row: {@code x + c + MAX} stops. A row
     * at {@code c} of -100 has one, on each side of {@code x >= y}. No value of {@code x} is said
     * to have no row because of it, so none is settled and none is a line the model draws: nothing
     * is shown of {@code x}.
     */
    @Test
    void aValueNoRowHeldAtTheNumberHasIsNotSaidToHaveNoRowAtAll() {
        Compilation compilation = measuredSource("""
                module demo

                data Y = Int invariant value >= 0 && value <= 10

                behavior f : (x: Int, c: Int, y: Y) -> Bool
                let f (x, c, y) = x + c + 9223372036854775807 - 9223372036854775807 >= c + y.value
                """);

        assertTrue(notShown(compilation), () -> offered(compilation));
    }
}
