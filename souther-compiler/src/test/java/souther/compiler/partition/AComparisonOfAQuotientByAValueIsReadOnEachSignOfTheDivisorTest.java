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

    /**
     * A quotient moved and weighed by numbers is the quotient against another number, the
     * relation turned where it is weighed by a number below nought: {@code 30 - 2 * (q + 1) > 0}
     * is {@code q < 14}, on each sign of the divisor.
     */
    @Test
    void aQuotientMovedAndWeighedByNumbersIsTheQuotientAgainstANumber() {
        for (String guard : List.of(ABOVE, BELOW)) {
            assertEquals(Set.copyOf(borders(guard, "a.pay / b.days < 14")),
                    Set.copyOf(borders(guard, "30 - 2 * (a.pay / b.days + 1) > 0")), guard);
            assertEquals(Set.copyOf(borders(guard, "a.pay / b.days >= 14")),
                    Set.copyOf(borders(guard, "(a.pay / b.days + 1) / 3 >= 5")), guard);
        }
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
     * A quotient on the left of a join is worked out first, so where its divisor is nought the run
     * stops there whatever the right half says: past a divisor held at nought, neither way of the
     * guard is taken. Read as the two halves side by side, a right half that fails would decide
     * the join, and the guard's failing way would be one a row is owed at.
     */
    @Test
    void aQuotientWorkedOutFirstStopsTheJoinAtANoughtDivisor() {
        String report = human(atANoughtDivisor("n / d >= 100 && c > 0"));
        assertTrue(report.contains("measurement: complete"), report);
        assertTrue(report.contains("no input takes 1 way through this body"), report);
        assertTrue(report.contains("no value can reach that arm"), report);
        assertFalse(report.contains("it goes through `else`"), report);
    }

    /**
     * And on the right, it is worked out only where the left half leaves the join open: past a
     * divisor held at nought, the guard fails wherever the left half does, and holds nowhere.
     */
    @Test
    void aQuotientWorkedOutSecondStopsOnlyWhereItIsReached() {
        String report = human(atANoughtDivisor("c > 0 && n / d >= 100"));
        assertTrue(report.contains("measurement: complete"), report);
        assertTrue(report.contains("no input takes 1 way through this body"), report);
        assertTrue(report.contains("it goes through `else`"), report);
    }

    /** The same of a choice: its condition is worked out before either arm. */
    @Test
    void aQuotientAChoiceIsDecidedByStopsItAtANoughtDivisor() {
        String report = human(atANoughtDivisor("if n / d >= 100 then c > 0 else c < 0"));
        assertTrue(report.contains("measurement: complete"), report);
        assertTrue(report.contains("no input takes 2 ways through this body"), report);
    }

    /**
     * What decides a choice is worked out before any of its cases, as an if's condition is, so a
     * quotient there is read wherever the comparison the choice stands in is: a choice in a value,
     * and the value a match selects by.
     */
    @Test
    void aQuotientDecidingAChoiceIsReadAsTheConditionOfAnIfIs() {
        for (String[] body : List.of(
                new String[] {ABOVE, "(if a.pay / b.days >= 100 then a.pay else c.pay) > 0"},
                new String[] {"""
                        guard b.days > 0 else No
                            let fine = match (if a.pay / b.days >= 100 then Ok else No) with
                                | Ok -> c.pay > 0
                                | No -> c.pay < 0""", "fine"})) {
            String report = human(MODEL.formatted(body[0], body[1]));
            assertTrue(report.contains("comparison@"), () -> body[1] + " compiles\n" + report);
            assertFalse(report.contains("a quotient by a value that is not a constant"),
                    () -> body[1] + "\n" + report);
        }
    }

    /** A body with a divisor held at nought, then a guard on {@code condition}. */
    private static String atANoughtDivisor(String condition) {
        return """
                module demo

                data Ok
                data No

                behavior f : (n: Int, d: Int, c: Int) -> Ok | No

                let f (n, d, c) = {
                    guard d == 0 else No
                    guard %s else No
                    Ok
                }
                """.formatted(condition);
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

    /** A body over a list of numbers and three numbers, with {@code %s} its guards. */
    private static final String OVER_A_LIST = """
            module demo

            data Ok
            data No

            behavior f : (xs: List<Int>, n: Int, a: Int, b: Int) -> Ok | No

            let f (xs, n, a, b) = {
                %s
                Ok
            }
            """;

    private static final String WHICH_FIRST = "which element a run reaches first";

    /**
     * Some element of a list the row writes meeting a comparison of a quotient by what the element
     * holds: the comparison draws its line on each element, and what the operation answers is read
     * where some element divides and meets it, or every element divides — the order is the row's,
     * and nothing else here reads it.
     */
    @Test
    void aQuotientByWhatEachElementHoldsIsReadOnEachElement() {
        for (String operation : List.of("List.any", "List.all")) {
            String report = human("""
                    module demo

                    data Month = { pay: Int, days: Int }
                    data Ok
                    data No

                    behavior f : (ms: List<Month>) -> Ok | No

                    let f (ms) = {
                        guard %s(m -> m.pay / m.days >= 100, ms) else No
                        Ok
                    }
                    """.formatted(operation));
            assertTrue(report.contains("read as f/-100 * ms[*].days + ms[*].pay"),
                    () -> operation + "\n" + report);
            assertFalse(report.contains("a quotient by a value that is not a constant"),
                    () -> operation + "\n" + report);
            assertFalse(report.contains(WHICH_FIRST), () -> operation + "\n" + report);
        }
    }

    /**
     * A quotient behind another part of what is stated of each element — worked out only where the
     * part before it holds — is read the same way, whether the operation asks some element or
     * counts how many: where the element answers is where the part before it fails, or holds and
     * the divisor is not nought.
     */
    @Test
    void aQuotientBehindAnotherPartOfTheElementsStatementIsReadToo() {
        for (String condition : List.of("List.any(x -> x > 5 && 100 / x >= 1, xs)",
                "List.length(List.filter(x -> x > 5 && 100 / x >= 1, xs)) >= 2")) {
            String report = human(OVER_A_LIST.formatted("guard " + condition + " else No"));
            assertTrue(report.contains("read as f/xs[*]"), () -> condition + "\n" + report);
            assertFalse(report.contains("a quotient by a value that is not a constant"),
                    () -> condition + "\n" + report);
        }
    }

    /**
     * A quotient by what each application of a closure is handed is read on each application: a
     * filter applies its closure to every value, and each value draws its line.
     */
    @Test
    void aQuotientByWhatEachApplicationIsHandedIsReadOnEach() {
        String report = human("""
                module demo

                behavior f : (n: Int, a: Int, b: Int) -> Bool

                let f (n, a, b) = List.length(List.filter(x -> n / x >= 1, [a, b])) >= 1
                """);
        assertTrue(report.contains("read as f/n: = a"), report);
        assertTrue(report.contains("read as f/n: = b"), report);
        assertFalse(report.contains("a quotient by a value that is not a constant"), report);
    }

    /**
     * A value written out after one whose divisor is held at nought is handed to no run: the first
     * stops every run there, so the second draws no line, and the operation comes out neither way.
     * The same whether the operation applies its closure to every value or stops at the first that
     * holds or fails — a run divides by the first before it asks anything of the second.
     */
    @Test
    void aValueNoRunGetsToDrawsNoLine() {
        for (String condition : List.of("List.any(x -> n / x >= 1, [a, b])",
                "List.all(x -> n / x >= 1, [a, b])",
                "List.length(List.filter(x -> n / x >= 1, [a, b])) >= 1",
                "List.length(List.filter(x -> n / x >= 1, [a, b])) >= 2")) {
            String model = OVER_A_LIST.formatted(
                    "guard a == 0 else No\n    guard " + condition + " else No");
            String report = human(model);
            assertTrue(bordersOfModel(model).stream().noneMatch(line -> line.contains("term=b")),
                    () -> condition + "\n" + report);
            assertTrue(report.contains("no input takes 2 ways through this body"),
                    () -> condition + "\n" + report);
        }
    }

    /**
     * A count of the elements a filter keeps is a number only where every element divided: a list
     * holding nought anywhere stops every run, so a guard that it holds one leaves the count
     * compared nowhere. Against one, the count is whether some element is kept; against more, a
     * count.
     */
    @Test
    void aCountOfWhatAFilterKeepsIsANumberOnlyWhereEveryElementDivided() {
        for (int least : List.of(1, 2)) {
            String report = human(OVER_A_LIST.formatted("""
                    guard List.any(x -> x == 0, xs) else No
                        guard List.length(List.filter(x -> 100 / x >= 1, xs)) >= %d else No"""
                    .formatted(least)));
            assertTrue(report.contains("no input takes 2 ways through this body"),
                    () -> least + "\n" + report);
            assertTrue(report.contains(
                    "the conditions on the way ask for what no input is at once"),
                    () -> least + "\n" + report);
        }
    }

    /**
     * A count compared in a case of how many an operation answers is a number only where every
     * statement it counts answered, and the case is read as the law states it all the same: how
     * many {@code List.take} answers is said in cases of how many it was handed, and here that is
     * a count of what a filter keeps.
     */
    @Test
    void aCountACaseOfASizeComparesIsReadAsTheCaseItIs() {
        for (String guard : List.of(
                "guard List.length(List.take(n, List.filter(x -> 100 / x >= 1, xs))) >= 2 else No",
                "guard List.length(List.take(n, List.filter(x -> x >= 1, xs))) >= 2 else No")) {
            String report = human(OVER_A_LIST.formatted(guard));
            assertTrue(report.contains("partition"), () -> guard + "\n" + report);
        }
    }

    /**
     * Where the order is not the row's to choose, which element a run stops at is not read. Two
     * operations each stopping at the first element meeting a quotient by what it holds may each
     * need another element first: of {@code [0, 100]} and {@code [100, 0]}, the first stops the
     * second guard and the second stops the first, and read in an order of the rows each would be
     * met — whether the closures are written in place or named first, and whatever the other one
     * ends a run for: a remainder by nought, or a sum with no place ({@code [0, MAX]} against
     * {@code [MAX, 0]} for {@code x + 1 == 1}). A list sorted first holds its elements in the order
     * of their values. And a list compared whole with another reads its order wherever the
     * comparison is made: {@code List.contains(xs, [[0, 100]])} holds only of {@code [0, 100]},
     * which stops every run, and the same elements the other way round are not that row.
     */
    @Test
    void whereTheRowsDoNotChooseTheOrderWhichElementARunStopsAtIsNotRead() {
        for (String guards : List.of("""
                guard List.any(x -> -100 / (x - 100) >= 1, xs) else No
                    guard List.any(x -> 100 / x >= 1, xs) else No""", """
                let first = x -> -100 / (x - 100) >= 1
                    let second = x -> 100 / x >= 1
                    guard List.any(first, xs) else No
                    guard List.any(second, xs) else No""", """
                guard List.any(x -> Int.floorMod(100, x - 100) == 0, xs) else No
                    guard List.any(x -> 100 / x >= 1, xs) else No""", """
                guard List.any(x -> x + 1 == 1, xs) else No
                    guard List.any(x -> 100 / x >= 1, xs) else No""",
                "guard List.any(x -> 100 / x >= 1, List.sort(xs)) else No", """
                guard List.contains(xs, [[0, 100]]) else No
                    guard List.any(x -> 100 / x >= 1, xs) else No""")) {
            String report = human(OVER_A_LIST.formatted(guards));
            assertTrue(report.contains(WHICH_FIRST), () -> guards + "\n" + report);
        }
    }

    /**
     * The control: what the library's facts say is the same in whatever order a list holds its
     * elements — how many it holds, whether it holds none, whether every element meets something
     * that ends no run, whether it holds a number — leaves the order to the rows beside the one
     * operation stopping at the first element meeting a quotient.
     */
    @Test
    void whatTheLibrarySaysIsTheSameInAnyOrderLeavesTheOrderToTheRows() {
        for (String first : List.of("List.length(xs) >= 2", "!List.isEmpty(xs)",
                "List.all(x -> x != 7, xs)", "List.contains(n, xs)")) {
            String guards = "guard " + first + " else No\n"
                    + "    guard List.any(x -> 100 / x >= 1, xs) else No";
            String report = human(OVER_A_LIST.formatted(guards));
            assertFalse(report.contains(WHICH_FIRST), () -> guards + "\n" + report);
        }
    }

    /**
     * An operation the library writes in the language ends a run for what its body ends one for:
     * {@code List.isEmpty} is {@code List.length(xs) == 0}, which ends none, so an operation stopping
     * at the first element meeting it is no second one beside the one meeting a quotient, written
     * through the operation or as its body.
     */
    @Test
    void anOperationTheLibraryWritesEndsARunForWhatItsBodyDoes() {
        for (String empty : List.of("List.isEmpty(m.tags)", "List.length(m.tags) == 0")) {
            String report = human("""
                    module demo

                    data Month = { pay: Int, days: Int, tags: List<Int> }
                    data Ok
                    data No

                    behavior f : (ms: List<Month>) -> Ok | No

                    let f (ms) = {
                        guard List.any(m -> %s, ms) else No
                        guard List.any(m -> m.pay / m.days >= 100, ms) else No
                        Ok
                    }
                    """.formatted(empty));
            assertFalse(report.contains(WHICH_FIRST), () -> empty + "\n" + report);
        }
    }

    /**
     * The control: a divisor the same on every application stops the first application where it
     * stops any, so the operation answers where every element divides, whatever the order — read
     * as such, and the comparison draws its line on each element. By the element's own divisor it
     * draws one too, on the list the row writes.
     */
    @Test
    void aQuotientByAValueTheSameOnEveryApplicationIsReadOnEach() {
        String byOne = human("""
                module demo

                data Month = { pay: Int, days: Int }

                behavior f : (ms: List<Month>, d: Int) -> Bool

                let f (ms, d) = List.any(m -> m.pay / d >= 100, ms)
                """);
        assertTrue(byOne.contains("read as f/-100 * d + ms[*].pay"), byOne);
        assertFalse(byOne.contains(WHICH_FIRST), byOne);
        String byEach = human("""
                module demo

                data Month = { pay: Int, days: Int }

                behavior f : (ms: List<Month>, d: Int) -> Bool

                let f (ms, d) = List.any(m -> m.pay / m.days >= 100, ms)
                """);
        assertTrue(byEach.contains("read as f/-100 * ms[*].days + ms[*].pay"), byEach);
        assertFalse(byEach.contains("a quotient by a value that is not a constant"), byEach);
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

    /**
     * Each line, without the name of the behavior it was drawn in.
     *
     * <p>The items written out in one order and not in a set's. A set's order is its hash table's,
     * which turns on the order its elements were put in and on a seed drawn per run, so two lines
     * with the same items were written out two ways.
     */
    private static List<String> described(List<BorderAssessment> lines) {
        assertNotNull(lines, "the behavior was measured");
        return lines.stream()
                .map(line -> (line.border().cut() + " " + new TreeSet<>(line.items().keySet()
                        .stream().map(String::valueOf).toList()))
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
