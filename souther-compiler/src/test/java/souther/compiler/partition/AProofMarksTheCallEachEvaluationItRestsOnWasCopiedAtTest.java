package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.LabeledRegion;
import souther.compiler.diag.msg.DeadBranchMessage;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A dead-branch proof names evaluations, and a place inside a helper is evaluated once for every
 * call the helper is copied into. Whatever the proof rests on — a negation, an arm of a
 * {@code match}, the left of a short-circuit, the application of a closure — it is marked at the
 * calls that made the copy it rests on. What the elaborator says of the copy a node stands in is
 * asked of the tree, where a proof does not name the node ({@code EveryEvaluationAProofMayRest…}).
 *
 * <p>Each case is a helper holding the evaluation and one call of it, so that the mark is at the
 * call and the name it carries is the helper's. The nested case reads the order too: the call
 * written in the caller comes before the call written in the helper's body.
 */
class AProofMarksTheCallEachEvaluationItRestsOnWasCopiedAtTest {

    private static final String GREATEST = "9223372036854775807";

    private static final String TYPES = """
            module w2

            data Ok
            data No
            data Answer = Ok | No
            """;

    /** The names of the helpers whose copies the dead-branch notes of {@code source} are about, in
     *  the order the notes say them. */
    private static List<String> copiesNamed(String source) {
        List<Diagnostic> dead = Compiler.compileWithWarnings(TYPES + source).warnings().stream()
                .filter(each -> each.code().equals("E1327")).toList();
        assertFalse(dead.isEmpty(), source);
        List<String> named = new ArrayList<>();
        for (Diagnostic one : dead) {
            for (LabeledRegion each : one.secondary()) {
                if (each.said() instanceof DeadBranchMessage.ThisCallMadeTheCopyTheProofIsAbout made) {
                    named.add(made.called());
                }
            }
        }
        return named;
    }

    @Test
    void aNegationInAHelperIsMarkedAtTheCallThatCopiedIt() {
        List<String> named = copiesNamed("""

                let flip (x: Int): Int = -x

                behavior f : (n: Int, b: Int) -> Answer
                let f (n, b) = {
                    guard n + %s == -1 else No
                    let flipped = flip(n)
                    if b > 3 then Ok else No
                }
                """.formatted(GREATEST));
        assertTrue(named.contains("flip"), named.toString());
    }

    @Test
    void anArmOfAMatchInAHelperIsMarkedAtTheCallThatCopiedIt() {
        List<String> named = copiesNamed("""

                let tag (a: Answer): Int = match a with
                    | Ok -> match a with
                        | Ok -> 1
                        | No -> 2
                    | No -> 3

                behavior f : (a: Answer) -> Int
                let f (a) = tag(a)
                """);
        assertTrue(named.contains("tag"), named.toString());
    }

    @Test
    void theLeftOfAShortCircuitInAHelperIsMarkedAtTheCallThatCopiedIt() {
        List<String> named = copiesNamed("""

                let gate (p: Int): Bool = p > 3 && (if p < 0 then true else false)

                behavior f : (b: Int) -> Answer
                let f (b) = if gate(b) then Ok else No
                """);
        // The left of the operator and the condition inside its right, each a decision made in the
        // copy, so each is marked at the call.
        assertEquals(2, Collections.frequency(named, "gate"), named.toString());
    }

    @Test
    void aHelperCalledFromAHelperIsMarkedAtBothCallsOutermostFirst() {
        List<String> named = copiesNamed("""

                let inner (x: Int, d: Date): Date = Date.addDays(x, d)
                let outer (x: Int, d: Date): Date = inner(x, d)

                behavior f : (n: Int, d: Date, b: Int) -> Answer
                let f (n, d, b) = {
                    guard n == %s else No
                    let moved = outer(n, d)
                    if b > 3 then Ok else No
                }
                """.formatted(GREATEST));
        int outer = named.indexOf("outer");
        int inner = named.indexOf("inner");
        assertTrue(outer >= 0 && inner > outer, named.toString());
    }

    /**
     * The application of a closure is a place of the helper like any other, and the note that says
     * a function is applied to every element is followed by the call that made the copy it is
     * about.
     */
    @Test
    void theApplicationOfAClosureInAHelperIsMarkedAtTheCallThatCopiedIt() {
        List<Diagnostic> dead = Compiler.compileWithWarnings(TYPES + """

                let moved (n: Int, d: Date): List<Date> =
                    List.map(k -> Date.addDays(k * n, d), [0, 1, 2])

                behavior f : (n: Int, d: Date, b: Int) -> Answer
                let f (n, d, b) = {
                    guard n == %s else No
                    let ys = moved(n, d)
                    if b > 3 then Ok else No
                }
                """.formatted(GREATEST)).warnings().stream()
                .filter(each -> each.code().equals("E1327")).toList();
        assertFalse(dead.isEmpty());
        for (Diagnostic one : dead) {
            List<LabeledRegion> marks = one.secondary();
            int applies = indexOf(marks, DeadBranchMessage.ThisAppliesAFunctionToEveryElement.class);
            assertTrue(applies >= 0 && applies + 1 < marks.size(), marks.toString());
            assertEquals(new DeadBranchMessage.ThisCallMadeTheCopyTheProofIsAbout("moved"),
                    marks.get(applies + 1).said());
        }
    }

    private static int indexOf(List<LabeledRegion> marks, Class<? extends DeadBranchMessage> kind) {
        for (int i = 0; i < marks.size(); i++) {
            if (kind.isInstance(marks.get(i).said())) {
                return i;
            }
        }
        return -1;
    }
}
