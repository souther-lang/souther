package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.Generator;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The rows for the cases a statement draws inside itself are admitted to the block only into the
 * room the rows before them leave, and a case left out is still one this run was asked about.
 *
 * <p>The room is the block's: the rows the fill, the lines and the rules put in it, counted once for
 * each stimulus. A case search told how much room the others took by what each composed was told a
 * guess, and the lines of one scope are not the lines of another.
 */
class ACaseRowTakesRoomInTheBlockOnlyWhereTheRowsBeforeItLeaveSomeTest {

    private static final String MODEL = """
            module m
            data Node = { v: Int, below: List<Node> }
            data Yes
            data No
            let anyBig (n: Node): Bool = n.v > 5 || List.any(c -> anyBig(c), n.below)
            behavior f : (t: Node, n: Int) -> Yes | No
            let f (t, n) = if n > 3 then Yes else if anyBig(t) then Yes else No
            example f
                | "the top" : (Node { v = 9, below = [] }, 0) -> Yes
                | "below" : (Node { v = 0, below = [ Node { v = 9, below = [] } ] }, 0) -> Yes
            """;

    @Test
    void aCaseRowIsAdmittedOnlyIntoTheRoomThatIsLeft() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> generated =
                Adequacy.generatedOf(compilation.db(), compilation.modules().getFirst());
        Adequacy.Filling filling = generated.get("f");
        List<Generator.GeneratedRow> before = new ArrayList<>(filling.tellingLinesApart());
        before.addAll(filling.rules().byRule().values());
        int others = Composition.stimuliBetween("f", filling.composed().offers(),
                List.of(before)).size();
        int withCases = Composition.stimuliBetween("f", filling.composed().offers(),
                List.of(before, filling.cases().byCase().values())).size();
        assertTrue(withCases > others,
                () -> "a case row is a row of its own: " + withCases + " against " + others);

        assertEquals(others, heldAt(generated, "f", others),
                "no room left, so no case row is admitted");
        assertEquals(others + 1, heldAt(generated, "f", others + 1),
                "and one row of room admits one");
        assertEquals(filling.cases().asked(),
                Composition.within(generated, null, others).get("f").cases().asked(),
                "a case left out is still one this run was asked about");
    }

    private static int heldAt(Map<String, Adequacy.Filling> generated, String behavior,
                              int rowLimit) {
        Adequacy.Filling fitted = Composition.within(generated, null, rowLimit).get(behavior);
        List<Generator.GeneratedRow> before = new ArrayList<>(fitted.tellingLinesApart());
        before.addAll(fitted.rules().byRule().values());
        return Composition.stimuliBetween(behavior, fitted.composed().offers(),
                List.of(before, fitted.cases().byCase().values())).size();
    }
}
