package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A value composed for a row is held to the rules of every value whose clauses reach the position
 * it is written at: the case the row is narrowed to, the element a container holds, and the value
 * above a name a case shares with its sum.
 *
 * <p>Each model fixes one field of a record and leaves the other to be composed, and the clause
 * relating the two is written where only one of those values can say it. A composer reading the
 * parameter's rules alone writes the other field at whatever its type stands for, and every row is
 * refused; the report then says nothing could show a row can be written. Composed under the right
 * rules, the row is written and the report says no row takes the rule, which is the rows the
 * examples hold falling short and not the search.
 *
 * <p>Every sum is asked with its cases declared both ways round: which case a value is composed
 * under is not something the order a sum lists them in decides.
 */
class AValueIsComposedUnderTheRulesOfEveryValueThatReachesItTest {

    private static final String NO_ROW_TAKES = "! no row takes a decision rule";

    private static final String NOTHING_COULD_SHOW = "nothing could show a row can be written";

    /** The relation is written in the record every case spreads, so it reaches the field through
     *  the case. */
    private static String spreadIntoTheCase(String cases) {
        return """
                module probe.r exposing ( C, A, B, S, f )

                data C = { lo: Int, hi: Int }
                    invariant lo <= hi

                data A = { ...C }

                data B = { ...C, x: Int }

                data S = %s

                behavior f : (s: S, n: Int) -> Int

                let f (s, n) = if s.hi == n - 1 then 1 else 0

                example f
                    | "one" : (A { lo = 0, hi = 5 }, 3) -> 0
                """.formatted(cases);
    }

    /** The relation is written in each case itself. */
    private static String writtenInTheCase(String cases) {
        return """
                module probe.r exposing ( C, A, B, S, f )

                data C = { lo: Int, hi: Int }

                data A = { ...C }
                    invariant lo <= hi

                data B = { ...C, x: Int }
                    invariant lo <= hi

                data S = %s

                behavior f : (s: S, n: Int) -> Int

                let f (s, n) = if s.hi == n - 1 then 1 else 0

                example f
                    | "one" : (A { lo = 0, hi = 5 }, 3) -> 0
                """.formatted(cases);
    }

    /**
     * Both the case and the record holding the sum relate the two fields. The case's relation is
     * met by a field one above the other and the holder's is not; a composer reading the case's
     * rules in place of the holder's writes the first.
     */
    private static String theHolderDecides(String cases) {
        return """
                module probe.r exposing ( Shared, A, B, Q, Holder, f )

                data Shared = { lo: Int, hi: Int }
                    invariant lo >= hi + 1

                data A = { ...Shared }

                data B = { ...Shared, x: Int }

                data Q = %s

                data Holder = { q: Q }
                    invariant q.lo >= q.hi + 8

                behavior f : (h: Holder, n: Int) -> Int

                let f (h, n) = if h.q.hi == n - 1 then 1 else 0

                example f
                    | "one" : (Holder { q = A { lo = 20, hi = 5 } }, 3) -> 0
                """.formatted(cases);
    }

    /**
     * The other way round: the holder's relation is met by a field one above the other and each
     * case's is not. Written in the cases and not in what they spread, so the holder cannot name
     * it, and a composer reading the holder's rules in place of the case's writes the first.
     */
    private static String theCaseDecides(String cases) {
        return """
                module probe.r exposing ( Shared, A, B, Q, Holder, f )

                data Shared = { lo: Int, hi: Int }

                data A = { ...Shared }
                    invariant lo >= hi + 8

                data B = { ...Shared, x: Int }
                    invariant lo >= hi + 8

                data Q = %s

                data Holder = { q: Q }
                    invariant q.lo >= q.hi + 1

                behavior f : (h: Holder, n: Int) -> Int

                let f (h, n) = if h.q.hi == n - 1 then 1 else 0

                example f
                    | "one" : (Holder { q = A { lo = 20, hi = 5 } }, 3) -> 0
                """.formatted(cases);
    }

    /** The two cases relate the fields in ways no value meets at once, so a composer holding a row
     *  to both cases' rules writes nothing under either. */
    private static String theCasesDisagree(String cases) {
        return """
                module probe.r exposing ( C, A, B, S, f )

                data C = { lo: Int, hi: Int }

                data A = { ...C }
                    invariant lo >= hi + 1

                data B = { ...C, x: Int }
                    invariant lo <= hi - 1

                data S = %s

                behavior f : (s: S, n: Int) -> Int

                let f (s, n) = if s.hi == n - 1 then 1 else 0

                example f
                    | "one" : (A { lo = 9, hi = 5 }, 3) -> 0
                """.formatted(cases);
    }

    @Test
    void aRelationSpreadIntoTheCaseHoldsTheFieldComposedBesideTheOneFixed() {
        for (String cases : new String[] {"A | B", "B | A"}) {
            assertComposed(cases, spreadIntoTheCase(cases), 1);
        }
    }

    @Test
    void aRelationWrittenInTheCaseHoldsTheFieldComposedBesideTheOneFixed() {
        for (String cases : new String[] {"A | B", "B | A"}) {
            assertComposed(cases, writtenInTheCase(cases), 1);
        }
    }

    @Test
    void theRulesOfTheValueHoldingTheSumAreKeptBesideTheCases() {
        for (String cases : new String[] {"A | B", "B | A"}) {
            assertComposed(cases, theHolderDecides(cases), 1);
        }
    }

    @Test
    void theRulesOfTheCaseAreKeptBesideTheValueHoldingTheSum() {
        for (String cases : new String[] {"A | B", "B | A"}) {
            assertComposed(cases, theCaseDecides(cases), 1);
        }
    }

    @Test
    void aCaseTheRowIsNotUnderHoldsItToNothing() {
        for (String cases : new String[] {"A | B", "B | A"}) {
            assertComposed(cases, theCasesDisagree(cases), 1);
        }
    }

    /**
     * An element's rules hold where the container holds one and nowhere else. The row with no
     * element at all is written, and so is the one whose element's fields the rule relates.
     */
    @Test
    void anElementsRulesHoldOnlyWhereThereIsAnElement() {
        String model = """
                module probe.r exposing ( Line, Order, f )

                data Line = { lo: Int, hi: Int }
                    invariant lo >= hi + 1

                data Order = { lines: List<Line> }

                behavior f : (o: Order, n: Int) -> Int

                let f (o, n) =
                    match List.get(0, o.lines) with
                        | None -> 2
                        | Some l -> if l.hi == n - 1 then 1 else 0

                example f
                    | "one" : (Order { lines = [Line { lo = 9, hi = 5 }] }, 3) -> 0
                """;

        assertComposed("", model, 2);
    }

    private static void assertComposed(String cases, String model, long rules) {
        String said = report(model);

        assertEquals(rules, count(said, NO_ROW_TAKES), cases + "\n" + said);
        assertFalse(said.contains(NOTHING_COULD_SHOW + " at 1 decision rule"),
                cases + "\n" + said);
    }

    private static long count(String said, String line) {
        return said.lines().filter(each -> each.contains(line)).count();
    }

    private static String report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).human(
                SourceRendering.namedByIdentity(compilation.texts()));
    }
}
