package souther.compiler.interaction;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.InputDomain;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A value this reading finds no path to is answered as one it has nothing to say about.
 *
 * <p>Two parts of a value whose every settling contradicts the other's leave the reading with
 * nothing: each part answers on its own, and no run has both of them answering. Whether that is
 * the body having no path there or this reading not following one is a question about how the
 * decisions on either side correlate, and nothing here asks it — what says each part answers is
 * read off the tree one part at a time.
 *
 * <p>So the empty answer is not published. Handed on, it reaches the reader that asks which ways a
 * value comes to a truth, where an empty enumeration is an answer and says the value never comes to
 * it. Said of both truths at once it takes both arms of a fork on that value away, and the reading
 * would be making a claim about the body off the back of its own silence.
 */
class NoArrivalsIsNotAProofThatNoValueArrivesTest {

    /**
     * A value whose two parts answer under opposite ways of one decision.
     *
     * <p>Each side arrives at a value — one where the flag holds and one where it fails — and the
     * arms that do not are arms nothing arrives at, so they are no ways either side is settled.
     * Put together there is no way both are settled at once.
     */
    private static final String CONTRADICTING_PARTS = """
            module example.parts

            behavior fee : (a: Bool, x: Int) -> Int

            let fee (a, x) =
                if (if a then x else unreachable "the flag holds here")
                        + (if a then unreachable "the flag fails here" else x) > 0
                    then (if a then 1 else 0) + (if x > 1 then 10 else 0)
                    else 0
            """;

    private static List<Interaction> read(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get(behavior);
        assertNotNull(body, "the behavior under test has a body");
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get(behavior);
        return Interactions.of(body, CoverageSites.of(checked.behaviorBodies()), inputs, symbols);
    }

    /**
     * A fork on such a value still has its arms walked, under the arms themselves.
     *
     * <p>Which is where a fork this reading cannot value has always left things. Taken as a value
     * settled to neither truth it would be a fork with no arm any row takes, and the meeting
     * written inside one of them would not be offered at all.
     */
    @Test
    void aForkOnAValueWithNoPathsStillHasItsArmsWalked() {
        List<Interaction> found = read(CONTRADICTING_PARTS, "fee");

        assertEquals(List.of(List.of(2, 2)), found.stream()
                        .map(group -> group.factors().stream()
                                .map(factor -> factor.outcomes().size()).toList())
                        .toList(),
                "the two charges in the arm meet: " + found);
        assertEquals(List.of("Arm"), found.get(0).reach().stream()
                        .map(decision -> decision.constrains().getClass().getSimpleName()).toList(),
                "under an arm, because the condition is one nothing here can value: " + found);
    }
}
