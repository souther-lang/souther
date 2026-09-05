package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.core.Core;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One body, two trees, and each says what its reader needs.
 *
 * <p>The tree a backend emits is an algorithm: an operation of the language is expanded into what it
 * does, because that is what has to be written out. The tree an analysis reads is a meaning: the
 * operation stands as itself, because what the analysis has rules about is
 * {@code String.startsWith} and not the walk it turns into.
 *
 * <p><b>Held here because both halves are load-bearing and neither is visible from the other.</b>
 * A reader after the meanings that was handed the algorithm finds every operation gone — with
 * nothing refusing it, no error to read, and a body that looks as though it states no rule about
 * its strings. That is what happened, and it went unnoticed because a comparison survives both
 * expansions: one kind of rule was found in the wrong tree and the other was not there to be found.
 *
 * <p>So the two facts are pinned together. Take either away and the pair stops saying anything: that
 * the operation stands somewhere is only interesting beside its being gone from the tree that runs,
 * and the emitted tree holding none is only a rule while some tree holds one.
 */
class TwoRepresentationsOfOneBodySayDifferentThingsTest {

    private static final String MODEL = """
            module example.two

            data Yes
            data No
            data Answer = Yes | No

            behavior pick : (code: String) -> Answer
            let pick (code) =
                if String.startsWith("JP", code) then Yes else No
            """;

    @Test
    void theAnalysisTreeHoldsTheOperationTheModelWrote() {
        Bodies.Elaborated checked = checkedModel();
        AnalysisBody read = checked.analysisBodies().get("pick");

        assertNotNull(read, "the behavior under test has a body for the analysis to read");
        assertFalse(keptCallsIn(read.core()).isEmpty(),
                "the analysis reads a tree where the language's own operations stand as themselves");
        assertEquals(List.of("startsWith"), keptCallsIn(read.core()),
                "which is the operation the model wrote, and only that one");
    }

    /**
     * And the emitted tree holds none, which is the half that makes the first one matter.
     *
     * <p>Not an incidental difference: what a backend emits has no operations left to stand, and a
     * representation that kept them is one it cannot write out.
     */
    @Test
    void andTheEmittedTreeHoldsNone() {
        Bodies.Elaborated checked = checkedModel();
        Core emitted = checked.behaviorBodies().get("pick");

        assertNotNull(emitted, "the behavior under test has a body to emit");
        assertEquals(List.of(), keptCallsIn(emitted),
                "the tree the backend writes out has expanded them into what they do");
    }

    /** And a rule this reads is written in the model rather than inside the operation's own
     *  implementation, which is the difference the two trees are about. */
    @Test
    void andTheTwoAreTreesOfTheSameBody() {
        Bodies.Elaborated checked = checkedModel();

        assertTrue(checked.behaviorBodies().containsKey("pick")
                        && checked.analysisBodies().containsKey("pick"),
                "one behavior, read both ways");
    }

    /** Every operation of the language left standing in {@code tree}, by the name it was written
     *  with, in the order the walk meets them. */
    private static List<String> keptCallsIn(Core tree) {
        List<String> found = new ArrayList<>();
        walk(tree, found);
        return found;
    }

    private static void walk(Core e, List<String> into) {
        if (e instanceof Core.PreservedCall call) {
            into.add(call.operation().name());
        }
        Core.forEachChild(e, child -> walk(child, into));
    }

    private static Bodies.Elaborated checkedModel() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(each -> each.diagnostic().code() + " " + each.diagnostic().primary())
                        .toList(),
                "the model under test compiles");
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test was checked");
        return checked;
    }
}
