package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where every run getting to a rule stops in an operation past where the representation of a
 * number stops, on the values of one place an input holds, the report says the invariant that
 * keeps every run from there: on the data holding the place, on the side the run stops past, and
 * as far out as it can be. The value itself is the domain's, so what is said is that bound, and
 * declaring it takes the stop away.
 *
 * <p>Not where a run stops where the clauses of a type a construction makes leave the number,
 * which the model already states and its own words are about; nor where it stops on a sum of two
 * inputs, which no bound on either alone keeps it from; nor on a place no data holds.
 */
class AnInvariantIsSuggestedWhereARunStopsAtARepresentationsEndTest {

    private static String report(String source) {
        Compilation compilation = ACompiledModel.measured(source, Adequacy.Asked.fullReport());
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static List<String> suggested(String report) {
        return report.lines().map(String::strip)
                .filter(line -> line.startsWith("· declaring `invariant ")).toList();
    }

    private static final String ABOVE = """
            module m

            data P = { x: Int }%s

            behavior f : (p: P) -> Bool
            let f (p) = p.x + 10 > 0
            """;

    @Test
    void aSumPastTheGreatestIntIsKeptFromByAnUpperBoundOnTheField() {
        String report = report(ABOVE.formatted(""));

        assertEquals(List.of("· declaring `invariant x <= 9223372036854775797` on P keeps every"
                + " run from stopping there; this is the furthest out the bound can be, and the"
                + " value to declare is the one the domain has"), suggested(report), report);
    }

    /** Declared, the run stops nowhere, and nothing is suggested. */
    @Test
    void theBoundDeclaredTakesTheStopAway() {
        String report = report(ABOVE.formatted("\n    invariant x <= 9223372036854775797"));

        assertFalse(report.contains("may stop a run"), report);
        assertFalse(report.contains("stop not resolved"), report);
        assertEquals(List.of(), suggested(report), report);
    }

    private static final String A_DAY_BACK = """
            module m

            data P = { birthday: Date }%s

            behavior f : (p: P) -> Bool
            let f (p) = Date.addDays(0 - 1, p.birthday) > Date("2000-01-01")
            """;

    @Test
    void aDateMovedPastTheFirstDayIsKeptFromByALowerBoundOnTheField() {
        String report = report(A_DAY_BACK.formatted(""));

        assertEquals(1, suggested(report).size(), report);
        assertTrue(suggested(report).getFirst().startsWith(
                "· declaring `invariant birthday >= Date(\"-999999999-01-02\")` on P"), report);
    }

    @Test
    void theBoundOnTheDateDeclaredTakesTheStopAway() {
        String report = report(A_DAY_BACK.formatted(
                "\n    invariant birthday >= Date(\"-999999999-01-02\")"));

        assertFalse(report.contains("may stop a run"), report);
        assertFalse(report.contains("stop not resolved"), report);
        assertEquals(List.of(), suggested(report), report);
    }

    /** A place whose own type is written under a name is bounded in that type, as its value. */
    @Test
    void aPlaceOfANamedTypeIsBoundedInThatType() {
        String report = report("""
                module m

                data Day = Int

                behavior f : (d: Day) -> Bool
                let f (d) = d.value + 1 > 0
                """);

        assertEquals(1, suggested(report).size(), report);
        assertTrue(suggested(report).getFirst().startsWith(
                "· declaring `invariant value <= 9223372036854775806` on Day"), report);
    }

    @Test
    void aSumOfTwoInputsIsKeptFromByNoBoundOnEither() {
        String report = report("""
                module m

                data P = { x: Int, y: Int }

                behavior f : (p: P) -> Bool
                let f (p) = p.x + p.y > 0
                """);

        assertTrue(report.contains("may stop a run"), report);
        assertEquals(List.of(), suggested(report), report);
    }

    @Test
    void aPlaceNoDataHoldsIsGivenNoBound() {
        String report = report("""
                module m

                behavior f : (x: Int) -> Bool
                let f (x) = x + 10 > 0
                """);

        assertTrue(report.contains("may stop a run"), report);
        assertEquals(List.of(), suggested(report), report);
    }

    /** A construction stops a run where the clauses of the type it makes leave the number, which
     *  the model states: the report's words on it are its own, and no bound is suggested. */
    @Test
    void aStopWhereAConstructionsClausesLeaveTheNumberIsGivenNoBound() {
        String report = report("""
                module m

                data Count = Int
                    invariant value >= 0

                data P = { n: Int }

                behavior f : (p: P) -> Bool
                let f (p) = Count(p.n).value > 3
                """);

        assertTrue(report.contains("may stop a run"), report);
        assertEquals(List.of(), suggested(report), report);
    }
}
