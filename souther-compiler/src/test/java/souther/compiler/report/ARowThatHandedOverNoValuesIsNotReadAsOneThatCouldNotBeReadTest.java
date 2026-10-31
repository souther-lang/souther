package souther.compiler.report;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderObligationPointAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ObligationSummary;
import souther.compiler.query.Weakening;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row that never handed its values over is not a row with values that could not be read.
 *
 * <p>What it built before it stopped or was refused is a prefix of the inputs and not the inputs,
 * so a border asked where such a row stands has no position to read and nothing to say about the
 * value. A row that stopped says so once, where it stopped, and the border it may have been at is
 * held open by that; one that was refused is evidence of nothing and holds nothing open.
 */
class ARowThatHandedOverNoValuesIsNotReadAsOneThatCouldNotBeReadTest {

    private static final String SPIN =
            "partial let spin (n: Int) : Int = if n < 0 then 0 else spin(n + 1)\n";

    private static final String ROWS =
            "    | \"low\" : (1, Hit(0)) -> 1\n    | \"high\" : (10, Hit(3)) -> 3\n";

    private static String model(String rows) {
        return """
                module m

                data Hit = Int
                    invariant value >= 0

                behavior grade : (n: Int, h: Hit) -> Int

                let grade (n, h) = if n >= 10 then h.value else n

                """ + SPIN + """

                example grade
                """ + rows;
    }

    private static List<Weakening> causes(List<String> codes, String rows) {
        return WrittenWitness.refusedOnly(codes, model(rows)).assessment().uncertainties()
                .stream()
                .filter(AdequacyUncertainty.ByWeakening.class::isInstance)
                .map(each -> ((AdequacyUncertainty.ByWeakening) each).cause())
                .toList();
    }

    /** The points of the behavior's borders left undecided, which is what a stop holds open. */
    private static int undecidedPoints(List<String> codes, String rows) {
        AdequacyReport report = WrittenWitness.refusedOnly(codes, model(rows));
        AdequacyReport.BehaviorReport behavior =
                report.modules().getFirst().behaviors().getFirst();
        return ObligationSummary.of(behavior.account(), BorderObligationPointAssessment::owed)
                .undecided().size();
    }

    /** The declaration's own borders, which no fork drew, held open by the same stop. */
    private static Set<Weakening> declarationCauses(List<String> codes, String rows) {
        return WrittenWitness.refusedOnly(codes, model(rows)).modules().getFirst()
                .declarationsWeakenedBy().causes();
    }

    @Test
    void aRowStoppedBeforeItsValuesLeavesAPointOfAForkBorderUndecided() {
        int without = undecidedPoints(List.of(), ROWS);
        int with = undecidedPoints(List.of("E1910"), ROWS + "    | \"spin\" : (spin(1), Hit(0)) -> 1\n");

        assertTrue(with > without, "points undecided: " + without + " before the row, " + with
                + " after");
    }

    @Test
    void aRowStoppedBeforeItsValuesHoldsTheBordersOfADeclarationOpenToo() {
        // No row at the invariant's own line, so a row that stopped may be the one standing on it.
        String apart = "    | \"low\" : (1, Hit(3)) -> 1\n    | \"high\" : (10, Hit(3)) -> 3\n";
        Set<Weakening> without = declarationCauses(List.of(), apart);
        Set<Weakening> with = declarationCauses(List.of("E1910"),
                apart + "    | \"spin\" : (1, Hit(spin(1))) -> 1\n");

        assertFalse(without.stream().anyMatch(Weakening.ObservationIncomplete.class::isInstance),
                () -> "nothing stopped yet: " + without);
        assertTrue(with.stream().anyMatch(Weakening.ObservationIncomplete.class::isInstance),
                () -> "the stop, at a border no fork drew: " + with);
    }

    @Test
    void aRowRefusedBeforeItsValuesLeavesTheUndecidedPointsAsTheyWere() {
        assertEquals(undecidedPoints(List.of(), ROWS),
                undecidedPoints(List.of("E1903"), ROWS + "    | \"bad\" : (1, Hit(-1)) -> 1\n"));
        assertEquals(declarationCauses(List.of(), ROWS),
                declarationCauses(List.of("E1903"), ROWS + "    | \"bad\" : (1, Hit(-1)) -> 1\n"));
    }

    @Test
    void aRowStoppedBeforeItsValuesHoldsABorderOpenByItsStopAndNotByAValueItCouldNotRead() {
        List<Weakening> causes = causes(List.of("E1910"),
                ROWS + "    | \"spin\" : (spin(1), Hit(0)) -> 1\n");

        assertTrue(causes.stream().anyMatch(Weakening.ObservationIncomplete.class::isInstance),
                () -> "the stop, once: " + causes);
        assertFalse(causes.stream().anyMatch(Weakening.BorderValueUnreadable.class::isInstance),
                () -> "and no value it could not read: " + causes);
    }

    @Test
    void aRowStoppedAtItsSecondValueIsNotTakenAsHavingWrittenItsFirst() {
        List<Weakening> causes = causes(List.of("E1910"),
                "    | \"high\" : (10, Hit(3)) -> 3\n    | \"spin\" : (1, Hit(spin(1))) -> 1\n");

        assertFalse(causes.stream().anyMatch(Weakening.BorderValueUnreadable.class::isInstance),
                () -> "no value it could not read: " + causes);
        assertTrue(causes.stream().anyMatch(Weakening.ObservationIncomplete.class::isInstance),
                () -> "a point the stopped row may stand at is open: " + causes);
    }

    /**
     * The first input of a row that stopped at its second is placed where it was written, in the
     * generator as in the classes. {@code Red} is covered by it and {@code Blue} is not, so a row
     * for {@code Blue} is offered and the position is not withheld.
     */
    @Test
    void theGeneratorPlacesTheInputsAStoppedRowGotThroughTheSameWayTheClassesDo() {
        Compilation compilation = Compilation.ofSource("""
                module m

                data Red
                data Blue
                data Color = Red | Blue

                behavior f : (color: Color, n: Int) -> Int

                let f (color, n) =
                    match color with
                        | Red -> n
                        | Blue -> 0

                """ + SPIN + """

                example f
                    | "red" : (Red, 1) -> 1
                    | "red then stops" : (Red, spin(1)) -> 0
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        Adequacy.Filling generated = Adequacy.generatedOf(compilation.db(), "m").get("f");
        assertFalse(generated.composed().rows().isEmpty(),
                () -> "a row for Blue is offered: " + generated.composed().reasons());
    }

    @Test
    void aRowRefusedBeforeItsValuesHoldsNothingOpen() {
        List<Weakening> causes = causes(List.of("E1903"),
                ROWS + "    | \"bad\" : (1, Hit(-1)) -> 1\n");

        assertFalse(causes.stream().anyMatch(Weakening.BorderValueUnreadable.class::isInstance),
                () -> "no value it could not read: " + causes);
    }

    @Test
    void aRowRefusedForTheNumberOfItsInputsHoldsNothingOpen() {
        List<Weakening> causes = causes(List.of("E1903"),
                ROWS + "    | \"two\" : (1, Hit(0), 5) -> 1\n");

        assertFalse(causes.stream().anyMatch(Weakening.BorderValueUnreadable.class::isInstance),
                () -> "no value it could not read: " + causes);
    }
}
