package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.SourceConstruct;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A truth a closure answers inside an operation's copy is the answer of the application written in
 * the closure, and never of the operation the closure was handed to.
 *
 * <p>A closure is applied inside the copy of the operation it was handed to, so the node it answers
 * at opens both copies. {@code List.map} answers a list; what is answered there is the truth of
 * {@code List.contains}, which the author wrote in the closure. Counted as both, the plan refused
 * the model as one where two applications answer at one node.
 */
class ATruthAClosureAnswersIsTheApplicationWrittenInItTest {

    @Test
    void aClosureHandedToAMappingAnswersWithWhatItApplies() {
        Compilation compilation = Compilation.ofSource("""
                module probe

                data Low
                data High

                behavior pick : (xs: List<List<Int>>) -> Low | High
                let pick (xs) =
                    if List.contains(true, List.map(ys -> List.contains(0, ys), xs)) then High
                    else Low
                """, "Main");
        compilation.answerEverything();
        Bodies.Elaborated checked =
                compilation.db().ask(new Bodies.Checked("probe")).value();
        assertNotNull(checked, () -> "the model compiles: " + compilation.errors());

        List<CoverageSites.AnswerSite> answers = checked.plan().answers("pick");
        assertEquals(List.of(SourceConstruct.CALL, SourceConstruct.CALL),
                answers.stream().map(each -> each.application().origin().kind()).toList(),
                () -> "the outer contains and the one in the closure, and not the mapping: "
                        + answers);
    }
}
