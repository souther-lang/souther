package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.report.AdequacyReport;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison of a quotient by a value with a number is read as the comparison of the dividend
 * with the number times the divisor, on each sign of the divisor.
 *
 * <p>The quotient is no form of what it divides, and what a comparison of it states is a line all
 * the same: above nought {@code n / d >= k} is {@code n >= k * d}, and below it the relation turns.
 * Which sign a run is on is the path's and the declarations', so where a guard or a type keeps the
 * divisor above nought, the comparison draws the line the comparison written out with the product
 * draws. The rows built at it are held against the run time's exact quotient.
 */
class AComparisonOfAQuotientByAValueIsReadOnEachSignOfTheDivisorTest {

    private static final String MODEL = """
            module demo

            data Month = { pay: Int, days: Int }
            data Ok
            data No

            behavior f : (a: Month, b: Month, c: Month) -> Ok | No

            let f (a, b, c) = {
                %s
                guard %s else No
                Ok
            }
            """;

    /** The comparison the issue was about: read, and what it states is all accounted for. */
    @Test
    void theQuotientUnderAPositiveDivisorIsReadAndAccountedFor() {
        String report = human(MODEL.formatted("guard b.days > 0 else No",
                "a.pay / b.days >= 100"));
        assertFalse(report.contains("a quotient by a value that is not a constant"), report);
        assertEquals(Set.copyOf(borders("guard b.days > 0 else No", "a.pay >= 100 * b.days")),
                Set.copyOf(borders("guard b.days > 0 else No", "a.pay / b.days >= 100")));
    }

    /**
     * Every relation, on either sign the path keeps the divisor to, is the comparison written out
     * with the relation turned where the divisor is below nought.
     */
    @Test
    void everyRelationOnEitherSignIsTheComparisonWrittenOut() {
        List<String> relations = List.of(">=", ">", "<=", "<", "==", "/=");
        List<String> turned = List.of("<=", "<", ">=", ">", "==", "/=");
        for (int i = 0; i < relations.size(); i++) {
            String rel = relations.get(i);
            assertEquals(Set.copyOf(borders("guard b.days > 0 else No",
                            "a.pay " + rel + " 100 * b.days")),
                    Set.copyOf(borders("guard b.days > 0 else No",
                            "a.pay / b.days " + rel + " 100")), "above nought: " + rel);
            assertEquals(Set.copyOf(borders("guard b.days < 0 else No",
                            "a.pay " + turned.get(i) + " 100 * b.days")),
                    Set.copyOf(borders("guard b.days < 0 else No",
                            "a.pay / b.days " + rel + " 100")), "below nought: " + rel);
        }
    }

    /**
     * And every point of the line is one some reading of it reaches, whichever side of the line
     * the value the source wrote belongs to and whichever sign the divisor is on.
     */
    @Test
    void everyPointOfTheLineIsReached() {
        for (String guard : List.of("guard b.days > 0 else No", "guard b.days < 0 else No")) {
            for (String condition : List.of("a.pay / b.days >= 100", "a.pay / b.days > 100",
                    "100 < a.pay / b.days", "a.pay / b.days == 100")) {
                String report = human(MODEL.formatted(guard, condition));
                assertFalse(report.contains("nothing could show"),
                        guard + " / " + condition + "\n" + report);
                assertFalse(report.contains("no row can stand"),
                        guard + " / " + condition + "\n" + report);
            }
        }
    }

    @Test
    void theQuotientWrittenOnTheRightIsTheSameRule() {
        assertEquals(Set.copyOf(borders("guard b.days > 0 else No", "a.pay / b.days > 100")),
                Set.copyOf(borders("guard b.days > 0 else No", "100 < a.pay / b.days")));
    }

    @Test
    void aQuotientGivenANameIsTheQuotient() {
        assertEquals(Set.copyOf(borders("guard b.days > 0 else No", "a.pay / b.days >= 100")),
                Set.copyOf(borders("""
                        guard b.days > 0 else No
                            let average = a.pay / b.days""", "average >= 100")));
    }

    /** A divisor its type keeps above nought is one no guard has to, and the line is the same. */
    @Test
    void aDivisorItsTypeKeepsAboveNoughtNeedsNoGuard() {
        String declared = """
                module demo

                data Month = { pay: Int, days: Int }
                    invariant days > 0
                data Ok
                data No

                behavior f : (a: Month, b: Month, c: Month) -> Ok | No

                let f (a, b, c) = {
                    guard %s else No
                    Ok
                }
                """;
        assertEquals(Set.copyOf(bordersOfModel(declared.formatted("a.pay >= 100 * b.days"))),
                Set.copyOf(bordersOfModel(declared.formatted("a.pay / b.days >= 100"))));
    }

    /**
     * A number no whole number writes is the number it is: a half below a hundred draws the line
     * at {@code a.pay - 99.5 * b.days}, and the rows built there stand on both sides of it.
     */
    @Test
    void aNumberAHalfFromAWholeOneIsTheNumberItIs() {
        List<String> half = borders("guard b.days > 0 else No", "a.pay / b.days >= 99.5m");
        assertTrue(half.stream().anyMatch(line -> line.contains("a.pay=1, b.days=-99.5")),
                half.toString());
        Set<Boolean> sides = new TreeSet<>();
        for (BigInteger[] row : rows(linesOfModel(MODEL.formatted("guard b.days > 0 else No",
                "a.pay / b.days >= 99.5m")))) {
            sides.add(row[0].multiply(BigInteger.TWO)
                    .compareTo(BigInteger.valueOf(199).multiply(row[1])) >= 0);
        }
        assertEquals(Set.of(false, true), sides);
    }

    /**
     * An average rounded to the nearest whole number is the quotient against the half below the
     * threshold, which is this rule after the rounding's.
     */
    @Test
    void aRoundedQuotientIsTheRoundingsLineReadThroughTheQuotient() {
        assertEquals(Set.copyOf(borders("guard b.days > 0 else No", "a.pay / b.days >= 99.5m")),
                Set.copyOf(borders("guard b.days > 0 else No",
                        "Rational.toInt(HALF_UP, a.pay / b.days) >= 100")));
    }

    /**
     * The rows built at the line stand on both sides of the comparison as the run time computes the
     * quotient, on each sign of the divisor and with the sign left open.
     */
    @Test
    void theRowsBuiltStandOnBothSidesOfTheExactQuotient() {
        for (String guard : List.of("guard b.days > 0 else No", "guard b.days < 0 else No",
                "guard b.days /= 0 else No")) {
            for (String rel : List.of(">=", ">", "<=", "<", "==", "/=")) {
                String condition = "a.pay / b.days " + rel + " 100";
                Set<Boolean> sides = new TreeSet<>();
                for (BigInteger[] row : rows(linesOfModel(MODEL.formatted(guard, condition)))) {
                    sides.add(holds(rel, row[0], row[1]));
                }
                assertEquals(Set.of(false, true), sides,
                        () -> "rows on both sides of: " + guard + " / " + condition);
            }
        }
    }

    /** With nothing settling the divisor's sign the comparison is read all the same, on each. */
    @Test
    void aDivisorOfEitherSignIsReadOnEach() {
        String report = human(MODEL.formatted("", "a.pay / b.days >= 100"));
        assertFalse(report.contains("a quotient by a value that is not a constant"), report);
    }

    /**
     * A quotient held against a value is no line: a value times the divisor is a product. And a
     * dividend no form says is left unread for what it is.
     */
    @Test
    void whatNoLineSaysStaysUnread() {
        assertTrue(human(MODEL.formatted("guard b.days > 0 else No", "a.pay / b.days >= c.pay"))
                .contains("a quotient by a value that is not a constant"));
        String product = human(MODEL.formatted("guard b.days > 0 else No",
                "a.pay * a.pay / b.days >= 100"));
        assertTrue(product.contains("not read: comparison"), product);
    }

    /** Whether {@code pay / days rel 100} holds, as the run time's exact quotient does. */
    private static boolean holds(String rel, BigInteger pay, BigInteger days) {
        // pay / days against 100, compared without dividing: the sign of days turns the order.
        int order = pay.multiply(BigInteger.valueOf(days.signum()))
                .compareTo(BigInteger.valueOf(100).multiply(days.abs()));
        return switch (rel) {
            case ">=" -> order >= 0;
            case ">" -> order > 0;
            case "<=" -> order <= 0;
            case "<" -> order < 0;
            case "==" -> order == 0;
            default -> order != 0;
        };
    }

    private static final Pattern MONTH = Pattern.compile("pay = (-?\\d+), days = (-?\\d+)");

    /** Every certified row's {@code a.pay} and {@code b.days}. */
    private static List<BigInteger[]> rows(List<BorderAssessment> lines) {
        List<BigInteger[]> out = new ArrayList<>();
        for (BorderAssessment border : lines) {
            for (ItemAssessment item : border.items().values()) {
                if (!(item instanceof ItemAssessment.Owed owed)) {
                    continue;
                }
                for (ItemAssessment.Attempt attempt : owed.searches().each()) {
                    if (attempt instanceof ItemAssessment.Attempt.Certified certified) {
                        Matcher a = MONTH.matcher(certified.row().inputs().get(0).text());
                        Matcher b = MONTH.matcher(certified.row().inputs().get(1).text());
                        assertTrue(a.find() && b.find(), certified.row().toString());
                        out.add(new BigInteger[] {new BigInteger(a.group(1)),
                                new BigInteger(b.group(2))});
                    }
                }
            }
        }
        return out;
    }

    private static List<String> borders(String guard, String condition) {
        return bordersOfModel(MODEL.formatted(guard, condition));
    }

    /**
     * Each line as what it is on and where, and the points a row is asked to stand at.
     *
     * <p>Not what the rule claims across it. A statement of several lines holds each line as the
     * relation it draws, so {@code n <= 100 * d} drawn below nought is held as the line it is and
     * not as the denial the source would write — the same line and the same points.
     */
    private static List<String> bordersOfModel(String model) {
        return linesOfModel(model).stream()
                .map(line -> line.border().cut() + " " + Set.copyOf(line.items().keySet()))
                .toList();
    }

    private static List<BorderAssessment> linesOfModel(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> read = Adequacy.readingsOf(compilation.db(), "demo");
        assertNotNull(read, "the model under test compiles");
        List<BorderAssessment> lines = read.get("f");
        assertNotNull(lines, "f was measured");
        return lines;
    }

    private static String human(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
