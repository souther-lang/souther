package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.ObjectMapper;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A run to an equality over {@code v} works out a number of {@code v} on the way, which stops a
 * run only where that number is too large: the product of a list of numbers, held to an
 * {@code Int} once it is multiplied out, and the span from one number to another, held to what a
 * {@code List} holds. Where the rules of {@code v} hold it so that the number is never too large,
 * the run gets past at every value and the equality is read at every value of {@code v}. Where
 * they leave a value it is too large at, a run may stop there and {@code v} is not shown reached
 * at every value.
 *
 * <p>Whether the number is too large is read off the numbers the rules leave each factor and
 * each end, multiplied or taken apart as written: a factor below nought turns the product's
 * sign, and a nought among the factors makes it nought whatever the others are.
 */
class AProductOrASpanOverNumbersTheRulesHoldShortIsGottenPastTest {

    private static final String NOT_SHOWN_REACHED = "relation_not_shown_reached_at_every_value";

    private static final String READ = "rule_relating_two_values";

    /** The greatest whole number whose square an {@code Int} holds. */
    private static final long GREATEST_SQUARED = 3_037_000_499L;

    /** The least whole number three times which an {@code Int} holds. */
    private static final long LEAST_TRIPLED = -3_074_457_345_618_258_602L;

    private static String model(String rule, String number) {
        return """
                module held

                data V = Int invariant %s

                behavior f : (v: V, ns: List<Int>) -> Bool
                let f (V(v), ns) = {
                    let m = %s
                    List.any(own -> own == v, ns) || m > 0
                }
                """.formatted(rule, number);
    }

    /** The same number worked out before an equality over strings, which reads no place of it. */
    private static String besideStrings(String rule, String number) {
        return """
                module beside

                data V = Int invariant %s

                behavior f : (v: V, others: List<String>, s: String) -> Bool
                let f (V(v), others, s) = {
                    let m = %s
                    List.any(own -> own == s, others) || m > 0
                }
                """.formatted(rule, number);
    }

    /** Why {@code v} is not read, each reason once in the order the report gives them. */
    private static List<String> whyVIsNotRead(String rule, String number) {
        return whyNotRead(model(rule, number), "v");
    }

    /** Why {@code position} of {@code source} is not read, each reason once in the order the
     *  report gives them. */
    private static List<String> whyNotRead(String source, String position) {
        Compilation model = ACompiledModel.measured(source,
                Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        JsonNode report = new ObjectMapper().readTree(AdequacyReport.of(model)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        List<String> out = new ArrayList<>();
        for (JsonNode module : report.path("modules")) {
            for (JsonNode behavior : module.path("behaviors")) {
                for (JsonNode each : behavior.path("partition").path("notRead")) {
                    String reason = each.path("reason").asString();
                    if (each.path("position").asString().equals(position)
                            && !out.contains(reason)) {
                        out.add(reason);
                    }
                }
            }
        }
        return out;
    }

    private static void reachedAtEveryValue(String rule, String number) {
        List<String> why = whyVIsNotRead(rule, number);
        assertTrue(why.contains(READ) && !why.contains(NOT_SHOWN_REACHED),
                () -> rule + " | " + number + " " + why);
    }

    private static void notShownReachedAtEveryValue(String rule, String number) {
        List<String> why = whyVIsNotRead(rule, number);
        assertTrue(why.contains(NOT_SHOWN_REACHED), () -> rule + " | " + number + " " + why);
    }

    /**
     * From nought to a hundred, {@code v} times itself is at most ten thousand and the span from
     * nought to it holds at most a hundred and one: neither stops a run. The same product written
     * as an operator is read the same.
     */
    @Test
    void aProductAndASpanOfANumberHeldSmallAreGottenPastAtEveryValue() {
        String rule = "value >= 0 && value <= 100";
        for (String number : List.of("List.product([v, v])", "v * v",
                "List.length(List.rangeInclusive(0, v))",
                "List.length(List.rangeInclusive(0 - v, v))")) {
            reachedAtEveryValue(rule, number);
        }
    }

    /** With no greatest value, a product of {@code v} and itself and a span to it may each be
     *  too large. */
    @Test
    void aProductAndASpanOfANumberWithNoGreatestMayStopTheRun() {
        for (String number : List.of("List.product([v, v])", "v * v",
                "List.length(List.rangeInclusive(0, v))")) {
            notShownReachedAtEveryValue("value >= 0", number);
        }
    }

    /**
     * A product or a span that may be too large stops a run only on the values of {@code v}: an
     * equality over strings beside it, which reads no place of {@code v}, is reached at every
     * string by a run with {@code v} small, and is read.
     */
    @Test
    void aProductOrASpanThatMayStopTiesOnlyThePlacesItReads() {
        for (String number : List.of("List.product([v, v])",
                "List.length(List.rangeInclusive(0, v))")) {
            List<String> why = whyNotRead(besideStrings("value >= 0", number), "s");
            assertEquals(List.of(READ), why, number);
        }
    }

    /**
     * The square of the greatest {@code v} is the whole of what decides: one past the greatest
     * whole number whose square an {@code Int} holds is a value the product stops at.
     */
    @Test
    void theProductStopsOnlyWhereTheSquareOfTheGreatestIsPastAnInt() {
        reachedAtEveryValue("value >= 0 && value <= " + GREATEST_SQUARED, "List.product([v, v])");
        notShownReachedAtEveryValue("value >= 0 && value <= " + (GREATEST_SQUARED + 1),
                "List.product([v, v])");
        notShownReachedAtEveryValue("value >= 0 && value <= 4000000000", "List.product([v, v])");
    }

    /**
     * A span from nought to a number past what a {@code List} holds stops the run there, and one
     * from a number to itself less a hundred is a span of none.
     */
    @Test
    void theSpanStopsWhereItIsLongerThanAListHolds() {
        notShownReachedAtEveryValue("value >= 0 && value <= 3000000000",
                "List.length(List.rangeInclusive(0, v))");
        reachedAtEveryValue("value >= 0 && value <= 3000000000",
                "List.length(List.rangeInclusive(v, v - 100))");
    }

    /**
     * A factor below nought: three times the least {@code v} is the least {@code Int} but one, and
     * three times one less is past it, while times less three it is the greatest but one. Where
     * a nought is among the factors the product is nought, however large the others are.
     */
    @Test
    void aFactorBelowNoughtTurnsTheProductAndANoughtMakesItNought() {
        reachedAtEveryValue("value >= " + LEAST_TRIPLED + " && value <= 0",
                "List.product([v, 3])");
        notShownReachedAtEveryValue("value >= " + (LEAST_TRIPLED - 1) + " && value <= 0",
                "List.product([v, 3])");
        reachedAtEveryValue("value >= " + LEAST_TRIPLED + " && value <= 0",
                "List.product([v, 0 - 3])");
        reachedAtEveryValue("value >= -100 && value <= 100", "List.product([v, v, v])");
        reachedAtEveryValue("value >= 0", "List.product([v, v, 0])");
    }
}
