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
import static org.junit.jupiter.api.Assertions.assertNotEquals;
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

    /**
     * One relation of each kind the reading tells apart: an order whose value holds at its line,
     * one whose value does not, and a value named. The relation is otherwise only handed on and
     * turned, which {@code Rel.turned} answers for every relation.
     */
    private static final List<String> RELATIONS = List.of(">=", ">", "==");

    private static final String ABOVE = "guard b.days > 0 else No";

    private static final String BELOW = "guard b.days < 0 else No";

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
        List<String> turned = List.of("<=", "<", "==");
        List<String[]> bodies = new ArrayList<>();
        for (int i = 0; i < RELATIONS.size(); i++) {
            String rel = RELATIONS.get(i);
            bodies.add(new String[] {ABOVE, "a.pay " + rel + " 100 * b.days"});
            bodies.add(new String[] {ABOVE, "a.pay / b.days " + rel + " 100"});
            bodies.add(new String[] {BELOW, "a.pay " + turned.get(i) + " 100 * b.days"});
            bodies.add(new String[] {BELOW, "a.pay / b.days " + rel + " 100"});
        }
        Map<String, List<BorderAssessment>> each = linesOfEach(modelOf(bodies));
        for (int i = 0; i < bodies.size(); i += 2) {
            assertEquals(Set.copyOf(described(each.get("f" + i))),
                    Set.copyOf(described(each.get("f" + (i + 1)))),
                    bodies.get(i + 1)[0] + " / " + bodies.get(i + 1)[1]);
        }
    }

    /**
     * And every point of the line is one some reading of it reaches, whichever side of the line
     * the value the source wrote belongs to and whichever sign the divisor is on.
     */
    @Test
    void everyPointOfTheLineIsReached() {
        List<String[]> bodies = new ArrayList<>();
        for (String guard : List.of(ABOVE, BELOW)) {
            for (String condition : List.of("a.pay / b.days >= 100", "a.pay / b.days > 100",
                    "100 < a.pay / b.days", "a.pay / b.days == 100")) {
                bodies.add(new String[] {guard, condition});
            }
        }
        String report = human(modelOf(bodies));
        assertFalse(report.contains("nothing could show"), report);
        assertFalse(report.contains("no row can stand"), report);
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
        List<String[]> bodies = new ArrayList<>();
        List<String> relations = new ArrayList<>();
        for (String guard : List.of(ABOVE, BELOW, "guard b.days /= 0 else No")) {
            for (String rel : RELATIONS) {
                bodies.add(new String[] {guard, "a.pay / b.days " + rel + " 100"});
                relations.add(rel);
            }
        }
        Map<String, List<BorderAssessment>> each = linesOfEach(modelOf(bodies));
        for (int i = 0; i < bodies.size(); i++) {
            Set<Boolean> sides = new TreeSet<>();
            for (BigInteger[] row : rows(each.get("f" + i))) {
                sides.add(holds(relations.get(i), row[0], row[1]));
            }
            String[] body = bodies.get(i);
            assertEquals(Set.of(false, true), sides,
                    () -> "rows on both sides of: " + body[0] + " / " + body[1]);
        }
    }

    /**
     * Where the divisor is nought the division aborts, and the comparison comes out no way: no
     * input takes the comparison holding past a divisor held at nought, nor failing, and neither is
     * a way a row is owed at.
     *
     * <p>Said of the ways and not of a line. Read as one side of the divisor's sign instead, a
     * divisor of nought would be a row the comparison holds or fails at, and a row composed for it
     * stops before it says either.
     */
    @Test
    void aDivisorHeldAtNoughtComesOutNoWay() {
        String report = human("""
                module demo

                data Ok
                data No

                behavior f : (n: Int, d: Int) -> Ok | No

                let f (n, d) = {
                    guard d == 0 else No
                    guard n / d >= 100 else No
                    Ok
                }
                """);
        assertTrue(report.contains("measurement: complete"), report);
        assertTrue(report.contains("no input takes 2 ways through this body"), report);
        assertFalse(report.contains("nothing could show"), report);
    }

    /**
     * With nothing settling the divisor's sign the comparison is read all the same, on each; and
     * where the division answers is no line of it, so the divisor carries the one line its sign
     * turns at and not a second at the nought no run divides by.
     */
    @Test
    void aDivisorOfEitherSignIsReadOnEach() {
        String report = human(MODEL.formatted("", "a.pay / b.days >= 100"));
        assertFalse(report.contains("a quotient by a value that is not a constant"), report);
        List<String> onTheDivisor = borders("", "a.pay / b.days >= 100").stream()
                .filter(line -> line.contains("term=b.days")).toList();
        assertEquals(1, onTheDivisor.size(), onTheDivisor.toString());
    }

    /**
     * A quotient inside what a closure states of each element is left unread where the closure is
     * read as a statement about the container: an element whose divisor is nought stops the whole
     * walk wherever the walk reaches it, which no statement of that element says.
     */
    @Test
    void aQuotientAsksNothingOfTheElementsAQuantifierIsOver() {
        String report = human("""
                module demo

                data Month = { pay: Int, days: Int }
                data Ok
                data No

                behavior f : (ms: List<Month>) -> Ok | No

                let f (ms) = {
                    guard List.any(m -> m.pay / m.days >= 100, ms) else No
                    Ok
                }
                """);
        assertTrue(report.contains("a quotient by a value that is not a constant"), report);
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

    /**
     * Whether {@code pay / days rel 100} holds, as the run time's exact quotient does — of a row
     * that reached the comparison, whose divisor is never nought: there the division aborts and the
     * row is no witness of either outcome.
     */
    private static boolean holds(String rel, BigInteger pay, BigInteger days) {
        assertNotEquals(0, days.signum(), "a row certified past the division divides by nought");
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

    /**
     * Every certified row's {@code a.pay} and {@code b.days}, at a line of the quotient's — one over
     * {@code a.pay}, which no guard on the divisor alone draws.
     */
    private static List<BigInteger[]> rows(List<BorderAssessment> lines) {
        List<BigInteger[]> out = new ArrayList<>();
        for (BorderAssessment border : lines) {
            if (!border.border().cut().toString().contains("a.pay")) {
                continue;
            }
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
        return described(linesOfModel(model));
    }

    /** Each line, without the name of the behavior it was drawn in. */
    private static List<String> described(List<BorderAssessment> lines) {
        assertNotNull(lines, "the behavior was measured");
        return lines.stream()
                .map(line -> (line.border().cut() + " " + Set.copyOf(line.items().keySet()))
                        .replaceAll("behavior=f\\d*", "behavior=f"))
                .toList();
    }

    /**
     * One model holding a behavior {@code f0}, {@code f1}, … for each guard and condition, so that
     * the comparisons a test sets beside one another are read in one compilation.
     */
    private static String modelOf(List<String[]> bodies) {
        StringBuilder out = new StringBuilder("""
                module demo

                data Month = { pay: Int, days: Int }
                data Ok
                data No
                """);
        for (int i = 0; i < bodies.size(); i++) {
            out.append("""

                    behavior f%d : (a: Month, b: Month, c: Month) -> Ok | No

                    let f%d (a, b, c) = {
                        %s
                        guard %s else No
                        Ok
                    }
                    """.formatted(i, i, bodies.get(i)[0], bodies.get(i)[1]));
        }
        return out.toString();
    }

    private static List<BorderAssessment> linesOfModel(String model) {
        List<BorderAssessment> lines = linesOfEach(model).get("f");
        assertNotNull(lines, "f was measured");
        return lines;
    }

    /** Every behavior's lines, by its name. */
    private static Map<String, List<BorderAssessment>> linesOfEach(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> read = Adequacy.readingsOf(compilation.db(), "demo");
        assertNotNull(read, "the model under test compiles");
        return read;
    }

    private static String human(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
