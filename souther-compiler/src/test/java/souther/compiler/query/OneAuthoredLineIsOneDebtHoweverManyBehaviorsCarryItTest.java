package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.partition.PointRole;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a report asks an author for is one row per authored line, and not one per position of every
 * behavior carrying the type.
 *
 * <p>Issue #1062 measured what the second costs. Over the fourteen modules of {@code
 * souther-examples}, 969 of the 1504 items a report marks are borders an {@code invariant} drew, and
 * they come from 75 clauses; in {@code crm} alone one clause of {@code UserId} is named 126 times,
 * at 74 behaviors. Discharging what that asks for means writing 126 rows that each stand at the same
 * point, for a rule the author wrote once — and no module can turn {@code --strict} on.
 */
class OneAuthoredLineIsOneDebtHoweverManyBehaviorsCarryItTest {

    /**
     * One clause carried by many behaviors is one debt, whatever the readings.
     *
     * <p>Counted rather than compared, because the failure is a debt appearing again: three
     * behaviors carry {@code UserId} at four positions between them, so a measure keyed on the
     * reading asks for the same row four times.
     */
    @Test
    void oneClauseCarriedByThreeBehaviorsIsOneDebt() {
        List<BorderAssessment> readings = readingsOf(CARRIED, "example.carried");
        assertEquals(4, readings.size(),
                () -> "the clause is read at every position carrying the type: "
                        + readings.stream().map(BorderAssessment::label).toList());

        // What a report and a build are handed. A debt is one item however many readings there
        // are, so the ON point of this clause is asked for once or not at all.
        List<Adequacy.Finding> declared = declaredFindings(CARRIED, "example.carried");
        assertEquals(List.of(), declared,
                () -> "one row is written at the boundary, so the line is not owed another: "
                        + declared.stream().map(each -> each.about().toString()).toList());
    }

    /**
     * A row at one of the positions discharges the debt at all of them.
     *
     * <p>The whole of what the collapse is worth, and what the count above does not say. Only
     * {@code schedule} is written a row at length 1; the debt is covered, because whether a row
     * standing at length 1 is believed is a question about {@code UserId} and neither
     * {@code touch} nor {@code review} says anything about the length of a user id.
     */
    @Test
    void aRowAtOnePositionDischargesTheDebtAtAllOfThem() {
        Map<String, BorderAssessment> byPosition = new java.util.LinkedHashMap<>();
        readingsOf(CARRIED, "example.carried").forEach(r -> byPosition.put(r.label(), r));
        assertEquals(List.of(true, false, false, false),
                byPosition.values().stream()
                        .map(each -> each.owedAt(PointRole.ON).hasRowWitness()).toList(),
                () -> "only one reading has a row at the point: " + byPosition.keySet());

        assertEquals(List.of(), declaredFindings(CARRIED, "example.carried"),
                "and the line is settled, because whether a row standing at length 1 is believed is"
                        + " a question about UserId");
    }

    /**
     * Take the one row away and the line is owed once, not once per position.
     *
     * <p>The other half of the measurement. Without it, an implementation that produced no declared
     * finding at all would pass both of the assertions above.
     */
    @Test
    void aLineNoRowStandsAtIsOwedOnce() {
        List<Adequacy.Finding> declared = declaredFindings(WELL_INSIDE, "example.carried");
        assertEquals(1, declared.size(),
                () -> "four readings and one row to write: "
                        + declared.stream().map(each -> each.about().toString()).toList());
        assertEquals(new FindingSubject.OfADeclaration(
                        souther.compiler.types.TypeSymbols.declared(
                                new souther.compiler.types.TypeKey("example.carried", "UserId"))),
                declared.get(0).subject(),
                "and it is asked of the declaration that wrote the rule");
    }

    /** Every finding the module's declarations are short of. */
    private static List<Adequacy.Finding> declaredFindings(String model, String module) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        List<Adequacy.Finding> findings =
                compilation.db().ask(new Adequacy.Findings(module)).value();
        assertNotNull(findings, "the model under test compiles");
        return findings.stream()
                .filter(each -> each.about() instanceof About.APointOfADeclaredBorder)
                .toList();
    }

    /**
     * Three behaviors carrying one type, one of them at two positions, and a row at the boundary
     * written for one of them.
     */
    private static final String CARRIED = """
            module example.carried

            data UserId = String
                invariant nonempty = String.length(value) >= 1

            data Draft = { owner: UserId, reviewer: UserId }
            data Task = { owner: UserId }
            data Note = { by: UserId }

            data Ok

            behavior schedule : (d: Draft) -> Ok
            let schedule (d) = Ok

            behavior touch : (t: Task) -> Ok
            let touch (t) = Ok

            behavior review : (n: Note) -> Ok
            let review (n) = Ok

            example schedule
                | "at the boundary" : (Draft { owner = UserId("x"), reviewer = UserId("yy") }) -> Ok

            example touch
                | "well inside" : (Task { owner = UserId("abcd") }) -> Ok

            example review
                | "well inside" : (Note { by = UserId("abcd") }) -> Ok
            """;

    /** The same three behaviors with no row at the boundary anywhere. */
    private static final String WELL_INSIDE =
            CARRIED.replace("UserId(\"x\")", "UserId(\"abc\")");

    /**
     * The points against the line agree across its readings; the points away from it do not.
     *
     * <p>Where the two halves of a border part. {@code ON} and {@code OFF} are values of the
     * quantity the rule cut, so what they ask is the same wherever the line is read — which is what
     * makes one row anywhere evidence for all of them. {@code IN} and {@code OUT} are the regions
     * either side, and where a region stops is settled by every other rule reaching that position:
     * {@code Cm}'s lower end runs to 150 at a length the record caps and runs on where nothing else
     * bounds it. A row well inside the second is not a row the first could hold at all.
     *
     * <p>Fixed here because the pull is to undo it. A border is one construct with four points, and
     * bringing all four under one debt reads as tidying — it would report a region covered on the
     * strength of a row that could not stand in it.
     */
    @Test
    void thePointsAgainstTheLineAgreeAcrossItsReadingsAndTheRegionsDoNot() {
        Map<String, BorderAssessment> byPosition = new java.util.LinkedHashMap<>();
        readingsOf(TWO_REGIONS, "example.regions").forEach(r -> byPosition.put(r.label(), r));
        BorderAssessment capped = byPosition.get("p.length = 0");
        BorderAssessment open = byPosition.get("o.straw = 0");
        assertNotNull(capped, byPosition.keySet().toString());
        assertNotNull(open, byPosition.keySet().toString());
        assertEquals(capped.border().obligation(), open.border().obligation(),
                "one clause of Cm drew the line both readings met");

        assertEquals(capped.border().demand(PointRole.ON), open.border().demand(PointRole.ON),
                "what a row at the line has to do is the same question about Cm");
        assertNotEquals(capped.border().demand(PointRole.IN), open.border().demand(PointRole.IN),
                "and what a row well inside has to do is a question about the position");
    }

    /** One newtype's lower end, read at a position a record caps and at one nothing else bounds. */
    private static final String TWO_REGIONS = """
            module example.regions

            data Cm = Int
                invariant nonneg = value >= 0

            data Parcel = { length: Cm }
                invariant fits = length.value <= 150

            data Order = { straw: Cm }

            data Ok

            behavior quote : (p: Parcel) -> Ok
            let quote (p) = Ok

            behavior mix : (o: Order) -> Ok
            let mix (o) = Ok

            example quote
                | "a" : (Parcel { length = Cm(10) }) -> Ok

            example mix
                | "a" : (Order { straw = Cm(10) }) -> Ok
            """;

    /**
     * A report prints the line under the declaration that drew it, once, and refuses over it.
     *
     * <p>Both halves, because they came apart. What the report shows and what the verdict rests on
     * are the same list read twice, and a walk over the behaviors alone left a declaration's line
     * out of the second — so a page printed a gap and said the rows met the bar underneath it.
     *
     * <p>Under the declaration, because that is where the author fixes it. Printed under a behavior
     * it would be printed under whichever one a walk reached first, and the reader sent there would
     * find a body that says nothing about the length of a user id.
     */
    @Test
    void aReportPrintsTheLineUnderItsDeclarationAndRefusesOverIt() {
        Compilation compilation = Compilation.ofSource(WELL_INSIDE, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        AdequacyReport report = AdequacyReport.of(compilation);
        String page = report.human(SourceNameResolver.identity());

        assertEquals(1, page.lines().filter(each -> each.contains("no row is at the ON point"))
                        .count(),
                () -> "four readings of one line and one item to read: " + page);
        assertTrue(page.contains("  UserId\n"
                        + "      ! no row is at the ON point String.length(value) = 1"),
                () -> "under the declaration that drew it, in the terms it was written in: " + page);
        assertEquals(AdequacyReport.AdequacyStatus.NOT_SATISFIED, report.adequacy(),
                "and what the page shows is what the verdict rests on");
    }

    /** Every reading of every line of {@code module}, as the measure holds them. */
    private static List<BorderAssessment> readingsOf(String model, String module) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                Adequacy.boundariesOf(compilation.db(), module);
        assertNotNull(boundaries, "the model under test compiles");
        return boundaries.values().stream().flatMap(List::stream).toList();
    }
}
