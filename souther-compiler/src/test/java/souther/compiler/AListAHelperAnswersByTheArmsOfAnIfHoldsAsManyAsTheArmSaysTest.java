package souther.compiler;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A list a helper answers in the arms of an {@code if} holds as many as the arm taken says, so
 * {@code List.get(0, ...)} finds an element on the arms that answer one.
 *
 * <p>Read as one list, its size is no position of the input, and the arm of the {@code match}
 * that takes the element is reached by a condition nothing is composed against: the points drawn
 * inside that arm are then owed rows no search can show are written.
 */
class AListAHelperAnswersByTheArmsOfAnIfHoldsAsManyAsTheArmSaysTest {

    private static String model(String roles) {
        return """
                module example.sizes

                data Role = Manager | Cfo
                data Within
                data Needs = { role: Role }

                behavior approval : (n: Int, m: Int) -> Within | Needs

                let rolesFor (n: Int): List<Role> = %s

                let approval (n, m) =
                    match List.get(0, rolesFor(n)) with
                        | None      -> Within
                        | Some role -> if m > 5 then Needs { role = role } else Within
                """.formatted(roles);
    }

    private static String report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** What the report says of a point no search shows a row can be written at. */
    private static final String NOTHING_COULD_SHOW = "nothing could show a row can be written";

    @Test
    void thePointsInTheArmThatTakesAnElementAreComposedAgainstTheArmsThatAnswerOne() {
        String report = report(model(
                "if n <= 10 then [ ] else if n <= 20 then [ Manager ] else [ Cfo ]"));
        assertFalse(report.contains(NOTHING_COULD_SHOW), report);
        assertTrue(report.contains("read as approval/m: = 6"), report);
    }

    @Test
    void theSameWhereNoArmAnswersOneLeavesNoRowAtThoseNotTaken() {
        String report = report(model("if n <= 10 then [ ] else [ ]"));
        assertFalse(report.contains("read as approval/m: = 6"), report);
    }
}
