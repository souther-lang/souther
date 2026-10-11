package souther.compiler.query;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A Bool input passed straight to a field of what a body answers is a condition of the rule, and a
 * row is seen taking it by the value the row wrote.
 *
 * <p>No construct of the model answers such a truth, so no run is recorded at it. The rows are the
 * only account there is of which way it came out, and a rule through it is placed from them rather
 * than left out of every reading of the run.
 */
class ABoolPassedStraightToAFieldIsReadOffTheRowTest {

    private static final String BODY = """
            module ql4

            data Q = { flag: Bool }
            data Below = { n: Int }

            behavior qual : (rawScore: Int, flag: Bool) -> Q | Below
                constructs Q, Below
            let qual (rawScore, flag) = {
                guard rawScore >= 60 else Below { n = 0 }
                Q { flag = flag }
            }

            example qual
            """;

    private static final String SIXTY_TRUE = "    | \"sixty\" : (60, true) -> Q { flag = true }\n";
    private static final String SIXTY_FALSE =
            "    | \"sixty-false\" : (60, false) -> Q { flag = false }\n";
    private static final String FIFTY_NINE_TRUE =
            "    | \"fifty-nine\" : (59, true) -> Below { n = 0 }\n";
    private static final String FIFTY_NINE_FALSE =
            "    | \"fifty-nine-false\" : (59, false) -> Below { n = 0 }\n";

    @Test
    void theRowsOfTheReportedModelAreEachPlacedAndTheUntakenRuleIsLeftUntaken() {
        DecisionEvidence.RowsPlaced read = readOf(SIXTY_TRUE + FIFTY_NINE_TRUE);
        assertEquals(2, read.rowsPlaced(), () -> "both rows took a rule: " + read);
        assertEquals(0, read.rowsNotPlaced(), () -> "and none went unplaced: " + read);
        assertEquals(2, read.rules().size(),
                () -> "two of the three rules, not the one with flag false: " + read);
    }

    @Test
    void aRowWithTheFlagFalseTakesTheRuleTheFlagTrueRowDoesNot() {
        DecisionEvidence.RowsPlaced read =
                readOf(SIXTY_TRUE + SIXTY_FALSE + FIFTY_NINE_TRUE);
        assertEquals(3, read.rowsPlaced(), () -> "every row took a rule: " + read);
        assertEquals(3, read.rules().size(), () -> "and each took a different one: " + read);
    }

    @Test
    void aRowThatStopsAtTheGuardTakesNoRuleOfTheFlag() {
        DecisionEvidence.RowsPlaced read = readOf(FIFTY_NINE_FALSE);
        assertEquals(1, read.rowsPlaced(), () -> "the row took a rule: " + read);
        assertEquals(1, read.rules().size(),
                () -> "the one the guard decides, whatever the flag was: " + read);
        assertTrue(read.everyRowWasWatched(), () -> "and it was watched: " + read);
    }

    private static DecisionEvidence.RowsPlaced readOf(String rows) {
        Compilation compilation = Compilation.ofSource(BODY + rows, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        DecisionEvidence evidence = compilation.db()
                .ask(new Adequacy.Decides(compilation.modules().get(0))).value().get("qual");
        return evidence.took().made()
                .orElseThrow(() -> new AssertionError("the rows were read: " + evidence.took()));
    }
}
