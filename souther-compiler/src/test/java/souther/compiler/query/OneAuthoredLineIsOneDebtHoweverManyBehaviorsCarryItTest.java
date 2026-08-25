package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.PointRole;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
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

        List<BorderObligationAssessment> debts = BorderObligationAssessment.across(readings);
        assertEquals(1, debts.size(),
                () -> "and all of them are the one line UserId's clause drew: "
                        + debts.stream().map(each -> each.origin().named()).toList());
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
        List<BorderObligationAssessment> debts =
                BorderObligationAssessment.across(readingsOf(CARRIED, "example.carried"));
        BorderObligationAssessment debt = debts.get(0);

        assertTrue(debt.owedAt(PointRole.ON).hasRowWitness(),
                "one behavior's row stands at the ON point, which settles the line");

        Map<String, BorderAssessment> byPosition = new java.util.LinkedHashMap<>();
        readingsOf(CARRIED, "example.carried").forEach(r -> byPosition.put(r.label(), r));
        assertEquals(List.of(true, false, false, false),
                byPosition.values().stream()
                        .map(each -> each.owedAt(PointRole.ON).hasRowWitness()).toList(),
                () -> "and the readings on their own say what they always said: "
                        + byPosition.keySet());
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
