package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.inputs.ElementQuestion;
import souther.compiler.inputs.ElementStep;
import souther.compiler.inputs.HeldIn;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Where an operation over a map is expanded, what is written down says which keys the map it
 * answers is keyed by, apart from where its values came from.
 *
 * <p>Asked of what the expansion wrote, because the tree after it holds a walk and no operation. A
 * map one operation answers and the next is handed is keyed by the keys of the map the first was
 * given — whatever the first did to the values — and a reader after the expansion has only this to
 * go on. The binding it is written on is the one the second expansion made for its map, which is
 * the one place both operations are in hand.
 */
class AnExpansionSaysWhichKeysTheMapItAnswersIsKeyedByTest {

    private static String handedOn(String operation) {
        return """
                module example.kept

                data Usage = { counts: Map<String, Int> }

                behavior popular : (u: Usage) -> Int

                let popular (u) = Map.size(Map.filterEntries((_, v) -> v < 9, %s))
                """.formatted(operation);
    }

    /** Taking entries out keeps both the values and the keys of the ones left. */
    @Test
    void aMapWithEntriesTakenOutHoldsTheSameValuesUnderTheSameKeys() {
        List<Said> said = saidOfEveryBinding(handedOn(
                "Map.filterEntries((_, v) -> v > 0, u.counts)"));
        assertEquals(1, said.stream()
                        .filter(each -> each.values() instanceof ElementStep.Through
                                && each.keys() instanceof ElementStep.Through)
                        .count(),
                () -> "one map is said to hold the values of another under its keys: " + said);
    }

    /** Rewriting the values makes new values and keeps every key. */
    @Test
    void aMapWithItsValuesRewrittenIsKeyedByTheKeysItHad() {
        List<Said> said = saidOfEveryBinding(handedOn("Map.mapValues((_, v) -> v + 1, u.counts)"));
        assertEquals(1, said.stream()
                        .filter(each -> each.values() instanceof ElementStep.Refused
                                && each.keys() instanceof ElementStep.Through)
                        .count(),
                () -> "one map is said to hold values made from another's, under its keys: "
                        + said);
    }

    /** What the expansion said of one binding, for its values and for its keys. */
    private record Said(BindingId binding, ElementStep values, ElementStep keys) {}

    private static List<Said> saidOfEveryBinding(String source) {
        Bodies.Elaborated checked = checked(source);
        ElementProvenance provenance =
                checked.elementBindings().get("popular").provenance();
        List<BindingId> bound = new ArrayList<>();
        collect(checked.behaviorBodies().get("popular"), bound);
        List<Said> out = new ArrayList<>();
        for (BindingId each : bound) {
            ElementStep values =
                    provenance.stepFrom(each, ElementQuestion.NAMED_POSITION, HeldIn.Part.ELEMENT);
            ElementStep keys =
                    provenance.stepFrom(each, ElementQuestion.NAMED_POSITION, HeldIn.Part.KEY);
            if (!(values instanceof ElementStep.NoEdge) || !(keys instanceof ElementStep.NoEdge)) {
                out.add(new Said(each, values, keys));
            }
        }
        return out;
    }

    private static void collect(Core e, List<BindingId> bound) {
        if (e instanceof Core.LetIn let && let.binder() != null
                && let.binder().binding() != null) {
            bound.add(let.binder().binding());
        }
        Core.forEachChild(e, child -> collect(child, bound));
    }

    private static Bodies.Elaborated checked(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        Bodies.Elaborated checked =
                compilation.db().ask(new Bodies.Checked(compilation.modules().get(0))).value();
        assertNotNull(checked, "the model under test compiles");
        return checked;
    }
}
