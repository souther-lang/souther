package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.ObjectMapper;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A run to an equality over {@code v} works out a whole number of {@code v} on the way, which
 * stops a run only at a value too large or at one pair of values: a quotient truncated toward
 * nought, which stops only on the least {@code Int} divided by minus one; a number rounded to a
 * whole one, held to an {@code Int}; and a number made a whole one only where it is whole, held
 * to an {@code Int}. Where the rules of {@code v} keep the run off those values, it gets past at
 * every value and the equality is read at every value of {@code v}. Where they leave one, a run
 * may stop there and {@code v} is not shown reached at every value.
 *
 * <p>A way of rounding chosen by the run is any of them, and each lands on the whole number at
 * or below the number or the one at or above it; a way written out is read as the one it is.
 */
class AQuotientOrAWholeNumberTheRulesHoldShortIsGottenPastTest {

    private static final String NOT_SHOWN_REACHED = "relation_not_shown_reached_at_every_value";

    private static final String READ = "rule_relating_two_values";

    /** The least {@code Int}, written as a run works it out. */
    private static final String LEAST = "0 - 9223372036854775807 - 1";

    /** The greatest {@code Int}. */
    private static final String GREATEST = "9223372036854775807";

    /** The greatest even number half of which, three times, an {@code Int} holds: three halves of
     *  it is one less than the greatest {@code Int}. */
    private static final long THREE_HALVES_FIT = 6_148_914_691_236_517_204L;

    private static String model(String rule, String number) {
        return """
                module held

                data V = Int invariant %s

                behavior f : (v: V, ns: List<Int>, up: Bool) -> Bool
                let f (V(v), ns, up) = {
                    let mode = if up then CEILING else FLOOR
                    let m = %s
                    List.any(own -> own == v, ns) || m > 0
                }
                """.formatted(rule, number);
    }

    private static String ofADecimal(String rule, String number) {
        return """
                module held

                data V = Decimal invariant %s

                behavior f : (v: V, ns: List<Decimal>, up: Bool) -> Bool
                let f (V(v), ns, up) = {
                    let mode = if up then CEILING else FLOOR
                    let m = %s
                    List.any(own -> own == v, ns) || m > 0
                }
                """.formatted(rule, number);
    }

    private static String quotient(String dividend, String divisor) {
        return """
                match Int.truncatingDivide(%s, %s) with
                        | Int as q -> q
                        | DivisionByZero -> 0""".formatted(dividend, divisor);
    }

    private static String wholeNumber(String number) {
        return """
                match Rational.toWholeNumber(%s) with
                        | Int as w -> w
                        | NotWhole -> 0""".formatted(number);
    }

    /** Why {@code v} is not read, each reason once in the order the report gives them. */
    private static List<String> whyVIsNotRead(String source) {
        Compilation model = ACompiledModel.measured(source,
                Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        JsonNode report = new ObjectMapper().readTree(AdequacyReport.of(model)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        List<String> out = new ArrayList<>();
        for (JsonNode module : report.path("modules")) {
            for (JsonNode behavior : module.path("behaviors")) {
                for (JsonNode each : behavior.path("partition").path("notRead")) {
                    String reason = each.path("reason").asString();
                    if (each.path("position").asString().equals("v") && !out.contains(reason)) {
                        out.add(reason);
                    }
                }
            }
        }
        return out;
    }

    private static void reachedAtEveryValue(String source) {
        List<String> why = whyVIsNotRead(source);
        assertTrue(why.contains(READ) && !why.contains(NOT_SHOWN_REACHED),
                () -> source + " " + why);
    }

    private static void notShownReachedAtEveryValue(String source) {
        List<String> why = whyVIsNotRead(source);
        assertTrue(why.contains(NOT_SHOWN_REACHED), () -> source + " " + why);
    }

    /**
     * Divided by minus one, {@code v} stops a run only at the least {@code Int}: from one above
     * it the quotient is an {@code Int}, and with the least among the values it is not.
     */
    @Test
    void aQuotientByMinusOneStopsOnlyWhereTheDividendMayBeTheLeastInt() {
        reachedAtEveryValue(model("value >= 0 && value <= 100", quotient("v", "0 - 1")));
        reachedAtEveryValue(model("value >= 0 - " + GREATEST + " && value <= 0",
                quotient("v", "0 - 1")));
        notShownReachedAtEveryValue(model("value <= 0", quotient("v", "0 - 1")));
    }

    /**
     * The least {@code Int} divided by {@code v} stops a run only where {@code v} may be minus
     * one: a divisor of nought answers a case, and one of minus two or less a quotient. A divisor
     * that is never minus one lets any dividend go.
     */
    @Test
    void aQuotientOfTheLeastIntStopsOnlyWhereTheDivisorMayBeMinusOne() {
        reachedAtEveryValue(model("value >= 0 && value <= 100", quotient(LEAST, "v")));
        reachedAtEveryValue(model("value >= 0 - 100 && value <= 0 - 2", quotient(LEAST, "v")));
        notShownReachedAtEveryValue(model("value >= 0 - 1 && value <= 100",
                quotient(LEAST, "v")));
        reachedAtEveryValue(model("value <= 0", quotient("v", "2")));
    }

    /**
     * Rounded by a way the run chooses, a decimal from nought to a hundred is a whole number an
     * {@code Int} holds; with no greatest it may be none.
     */
    @Test
    void aDecimalRoundedByAWayTheRunChoosesIsGottenPastWhereItsRangeIsHeld() {
        reachedAtEveryValue(ofADecimal("value >= 0.0m && value <= 100.0m",
                "Decimal.toInt(mode, v)"));
        notShownReachedAtEveryValue(ofADecimal("value >= 0.0m", "Decimal.toInt(mode, v)"));
    }

    /**
     * Half past the greatest {@code Int}, a way the run chooses may round up past it, and the
     * greatest itself rounds to itself every way. Rounded down as written, half past rounds to
     * the greatest.
     */
    @Test
    void aWayTheRunChoosesMayRoundHalfPastTheGreatestIntUp() {
        reachedAtEveryValue(ofADecimal("value >= 0.0m && value <= " + GREATEST + ".0m",
                "Decimal.toInt(mode, v)"));
        notShownReachedAtEveryValue(ofADecimal("value >= 0.0m && value <= " + GREATEST + ".5m",
                "Decimal.toInt(mode, v)"));
        reachedAtEveryValue(ofADecimal("value >= 0.0m && value <= " + GREATEST + ".5m",
                "Decimal.toInt(FLOOR, v)"));
        notShownReachedAtEveryValue(model("value >= 0 && value <= " + (THREE_HALVES_FIT + 1),
                "Rational.toInt(mode, v / 2 * 3)"));
        reachedAtEveryValue(model("value >= 0 && value <= " + (THREE_HALVES_FIT + 1),
                "Rational.toInt(DOWN, v / 2 * 3)"));
    }

    /**
     * Three halves of {@code v} is a whole number an {@code Int} holds from nought to a hundred,
     * and may be one past it with no greatest {@code v}.
     */
    @Test
    void aWholeNumberOfANumberHeldSmallIsGottenPastAtEveryValue() {
        reachedAtEveryValue(model("value >= 0 && value <= 100", wholeNumber("v / 2 * 3")));
        reachedAtEveryValue(model("value >= 0", wholeNumber("v / 2")));
        notShownReachedAtEveryValue(model("value >= 0", wholeNumber("v / 2 * 3")));
    }

    /**
     * Where three halves of the greatest {@code v} is half past the greatest {@code Int}, that is
     * no whole number and answers a case, and every whole number below it is an {@code Int}. One
     * more and three halves of it is a whole number past the greatest.
     */
    @Test
    void aNumberHalfPastTheGreatestIntIsNoWholeNumberToStopOn() {
        reachedAtEveryValue(model("value >= 0 && value <= " + THREE_HALVES_FIT,
                wholeNumber("v / 2 * 3")));
        reachedAtEveryValue(model("value >= 0 && value <= " + (THREE_HALVES_FIT + 1),
                wholeNumber("v / 2 * 3")));
        notShownReachedAtEveryValue(model("value >= 0 && value <= " + (THREE_HALVES_FIT + 2),
                wholeNumber("v / 2 * 3")));
    }
}
