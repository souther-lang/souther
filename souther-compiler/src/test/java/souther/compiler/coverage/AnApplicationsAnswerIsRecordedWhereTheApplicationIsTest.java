package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.Citation;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Where an application of one of the language's operations answers is recorded at the
 * application, and the places are listed in the order the body writes them.
 *
 * <p>Two ways this was not so. A binding an author wrote was read as standing in the copy its body
 * opens, so an emptiness check that was a {@code let}'s whole body was recorded where the
 * {@code let} is. And the places were listed in the order their nodes hash in, which is a
 * different order every run — so which place a reading took for an application written more than
 * once was a different one every run.
 */
class AnApplicationsAnswerIsRecordedWhereTheApplicationIsTest {

    private static final String MODEL = """
            module probe.answered

            data Order = { first: List<Int>, second: List<Int>, third: List<Int> }

            behavior bound : (o: Order) -> Bool
            let bound (o) = {
                let ls = o.first
                List.isEmpty(ls)
            }

            behavior chain : (o: Order) -> Int
            let chain (o) =
                if List.isEmpty(o.first) then 1
                else if List.isEmpty(o.second) then 2
                else if List.isEmpty(o.third) then 3
                else 4
            """;

    /** An emptiness check that is a binding's whole body is recorded at the check. */
    @Test
    void anAnswerUnderABindingIsRecordedAtTheApplication() {
        Bodies.Elaborated checked = checked();
        List<CoverageSites.AnswerSite> answers = checked.plan().answers("bound");
        assertEquals(1, answers.size(), () -> "one application answers: " + answers);
        assertEquals(writtenAt(checked, "bound"),
                answers.stream().map(CoverageSites.AnswerSite::writtenAt).toList(),
                "recorded where the application is written, and not where the binding is");
    }

    /** The places are listed in the order the body writes the applications. */
    @Test
    void thePlacesAreListedInTheOrderTheBodyWritesThem() {
        Bodies.Elaborated checked = checked();
        assertEquals(writtenAt(checked, "chain"),
                checked.plan().answers("chain").stream().map(CoverageSites.AnswerSite::writtenAt)
                        .toList());
    }

    /** Where each emptiness check of {@code behavior} is written, in the order it is written. */
    private static List<Citation> writtenAt(Bodies.Elaborated checked, String behavior) {
        Core body = checked.analysisBodies().get(behavior).core();
        List<Citation> out = new ArrayList<>();
        collect(body, out);
        assertEquals(false, out.isEmpty(), "the body applies an emptiness check");
        return out;
    }

    private static void collect(Core e, List<Citation> out) {
        if (Core.withoutStanding(e) instanceof Core.PreservedCall call
                && call.declared().operation().equals(
                        ValueName.Stdlib.operation("List", "isEmpty"))) {
            out.add(Citation.of(call.pos()));
        }
        for (CoreStructure.Child child : CoreStructure.childrenOf(e)) {
            collect(child.node(), out);
        }
    }

    private static Bodies.Elaborated checked() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles: " + compilation.errors());
        return checked;
    }
}
