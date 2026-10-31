package souther.compiler.report;

import souther.compiler.query.Weakening;

import org.junit.jupiter.api.Test;

import java.util.List;

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
