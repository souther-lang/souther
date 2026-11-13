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

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A number rounded to an {@code Int} stops a run only where it rounds past one, so where the
 * numbers it is made of are held small it gets past at every value of {@code v}. Made through a
 * call of the library, those are the numbers the library says the call answers: a call that
 * computes what an operator does is that operator over its arguments ({@code Decimal.add}), a
 * call that answers a form of its arguments is that form ({@code Decimal.fromInt}), and a name an
 * arm binds to a quotient is that quotient. With no greatest {@code v}, it may round past.
 */
class ARangeIsCarriedThroughACallTheLibrarySaysTheArithmeticOfTest {

    private static final String NOT_SHOWN_REACHED = "relation_not_shown_reached_at_every_value";

    private static final String READ = "rule_relating_two_values";

    private static String model(String type, String rule, String number) {
        return """
                module held

                data V = %s invariant %s

                behavior f : (v: V, ns: List<%s>, up: Bool) -> Bool
                let f (V(v), ns, up) = {
                    let mode = if up then CEILING else FLOOR
                    let m = %s
                    List.any(own -> own == v, ns) || m > 0
                }
                """.formatted(type, rule, type, number);
    }

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

    /** Read at every value where {@code v} is held to {@code held}, and not shown to be where it
     *  is held to {@code open}. */
    private static void heldSmallOnly(String type, String held, String open, String number) {
        List<String> small = whyVIsNotRead(model(type, held, number));
        assertTrue(small.contains(READ) && !small.contains(NOT_SHOWN_REACHED),
                () -> number + " " + small);
        List<String> large = whyVIsNotRead(model(type, open, number));
        assertTrue(large.contains(NOT_SHOWN_REACHED), () -> number + " " + large);
    }

    private static void ofAnInt(String number) {
        heldSmallOnly("Int", "value >= 0 && value <= 100", "value >= 0", number);
    }

    private static void ofADecimal(String number) {
        heldSmallOnly("Decimal", "value >= 0.0m && value <= 100.0m", "value >= 0.0m", number);
    }

    @Test
    void aCallComputingWhatAnOperatorDoesIsThatOperator() {
        ofADecimal("Decimal.toInt(mode, Decimal.add(v, v))");
        ofADecimal("Decimal.toInt(mode, Decimal.subtract(v, 1.0m) * 3.0m)");
        ofAnInt("Rational.toInt(mode, Int.multiply(v, 3) / 2)");
    }

    /**
     * A name an arm binds to the number a call answers in that arm's case is that number: a
     * quotient of {@code v} truncated toward nought, which lies between the quotients of the ends
     * of {@code v}, the order turned by a divisor below nought.
     */
    @Test
    void aNameAnArmBindsToAQuotientIsThatQuotient() {
        ofAnInt("""
                match Int.truncatingDivide(v, 2) with
                        | Int as q -> q * 92233720368547758
                        | DivisionByZero -> 0""");
        ofAnInt("""
                match Int.truncatingDivide(v, 0 - 2) with
                        | Int as q -> Rational.toInt(mode, q / 2 * 5)
                        | DivisionByZero -> 0""");
    }

    /**
     * What a call of a {@code Rational} operation computes is said of its arguments, though its
     * answer is on no carrier, so its range is read the way the same written with operators is.
     */
    @Test
    void aCallOfARationalOperationIsTheArithmeticItComputes() {
        ofAnInt("Rational.toInt(mode, Rational.fromInt(v) * 92233720368547758)");
        ofAnInt("Rational.toInt(mode, Rational.add(Rational.fromInt(v), v / 2))");
        ofAnInt("Rational.toInt(mode, Rational.subtract(Rational.fromInt(v), v / 2)"
                + " * 92233720368547758)");
        ofAnInt("Rational.toInt(mode, Rational.multiply(v / 2, v / 2))");
        ofAnInt("Rational.toInt(mode, Rational.fromInt(v) / Rational.fromInt(2)"
                + " * 92233720368547758)");
        ofAnInt("Rational.toInt(mode, Rational.divide(Rational.fromInt(v), Rational.fromInt(2))"
                + " * 92233720368547758)");        ofADecimal("Rational.toInt(mode, Rational.fromDecimal(v) * 92233720368547758)");
    }

    /** A divisor that may be nought is a stop the range does not answer for, call or operator. */
    @Test
    void aDivisorThatMayBeNoughtIsNotShownToGetPast() {
        for (String number : List.of(
                "Rational.toInt(mode, Rational.divide(Rational.fromInt(1), Rational.fromInt(v)))",
                "Rational.toInt(mode, Rational.fromInt(1) / Rational.fromInt(v))",
                "Rational.toInt(mode, Rational.divide(Rational.fromInt(1), Rational.fromInt(0)))")) {
            List<String> held = whyVIsNotRead(
                    model("Int", "value >= 0 && value <= 100", number));
            assertTrue(held.contains(NOT_SHOWN_REACHED), () -> number + " " + held);
        }
    }

    @Test
    void aCallAnsweringAFormOfItsArgumentsIsThatForm() {
        ofAnInt("Decimal.toInt(mode, Decimal.fromInt(v) * 92233720368547758.0m)");
        ofAnInt("""
                match Int.truncatingDivide(v, 2) with
                        | Int as q -> Decimal.toInt(mode, Decimal.fromInt(q) * 184467440737095516.0m)
                        | DivisionByZero -> 0""");
    }
}
