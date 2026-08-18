package souther.compiler;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What an arm opened decides which value the arm's name is. It does not decide whether a construction
 * inside the arm is one an author is asked to guard.
 *
 * <p>Following what a name was given now reaches through a {@code match}: an arm opening text written
 * into the source opens that text, where before the text stopped at the match. Which is right about
 * the value and says nothing about the construction standing under the arm — that construction is
 * built from what the arm bound, and what an author can do about it is the same whether the value
 * came from a parameter or was written out three lines up.
 *
 * <p>Held as the two answering alike rather than as either answer on its own. What a construction over
 * an unproven value comes to is one thing; that it comes to the same thing under both is what this is
 * about, and a rule that read the written case differently would show up here and nowhere in the
 * corpus, which writes no such match.
 */
class AConstructionUnderAnArmIsJudgedTheSameWhateverItOpenedTest {

    /** The scrutinee is a value handed in: nothing here says what it holds. */
    private static final String OPENED_FROM_A_PARAMETER = """
            module demo

            data Positive = Int
                invariant value > 0

            data Held = { n: Int }
            data Missing
            data Answer = Held | Missing

            data Box = { p: Positive }

            behavior boxed : (a: Answer) -> Box constructs Box, Positive
            let boxed (a) =
                match a with
                    | Held as h -> Box { p = Positive(h.n) }
                    | Missing -> Box { p = Positive(1) }
            """;

    /** The same construction, over a scrutinee written into the source. */
    private static final String OPENED_FROM_WRITTEN_TEXT = """
            module demo

            data Positive = Int
                invariant value > 0

            data Held = { n: Int }
            data Missing
            data Answer = Held | Missing

            data Box = { p: Positive }

            behavior boxed : (x: Int) -> Box constructs Box, Positive, Held
            let boxed (x) = {
                let written: Answer = Held { n = 5 }
                match written with
                    | Held as h -> Box { p = Positive(h.n) }
                    | Missing -> Box { p = Positive(1) }
            }
            """;

    @Test
    void aConstructionUnderAnArmIsJudgedTheSameWhateverTheArmOpened() {
        assertEquals(warnings(OPENED_FROM_A_PARAMETER), warnings(OPENED_FROM_WRITTEN_TEXT),
                "what an arm opened is not what decides whether a construction is said about");
    }

    /** And what both say is what an unproven construction is said about: the field the arm's name is
     * read at is not text, whatever the value behind the name was written as, so nothing settles it
     * and an author is told. */
    @Test
    void andWhatBothSayIsThatTheConstructionIsNotSettled() {
        assertEquals(1, warnings(OPENED_FROM_A_PARAMETER));
        assertEquals(1, warnings(OPENED_FROM_WRITTEN_TEXT));
    }

    private static long warnings(String module) {
        return Compiler.compileWithWarnings(module).warnings().stream()
                .filter(d -> d.severity() == souther.compiler.diag.Severity.WARNING)
                .count();
    }
}
