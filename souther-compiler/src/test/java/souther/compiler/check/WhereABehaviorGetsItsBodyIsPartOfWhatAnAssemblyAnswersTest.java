package souther.compiler.check;

import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Where each behavior gets its body is answered beside the tree an assembly projects, and compared
 * beside it.
 *
 * <p>A store decides whether anything downstream is asked again by comparing the answer it
 * recomputed with the one it held. A module on the path republished with an implemented behavior
 * now left to Java reads back as the same tree, so an assembly that compared only its tree would be
 * the old answer to every reader of it — each of them still told the behavior has a body.
 */
class WhereABehaviorGetsItsBodyIsPartOfWhatAnAssemblyAnswersTest {

    private static final String SOURCE = """
            module m exposing ( Out, go )
            data Out = { n: Int }
            behavior go : (n: Int) -> Out
                constructs Out
            let go (n) = Out { n = n }
            """;

    @Test
    void twoAssembliesThatDifferOnlyInWhereABodyComesFromAreTwoAnswers() {
        CheckSurface itsOwn = Compilation.ofSource(SOURCE, "Main").db()
                .ask(new Shapes.CheckSurface("m")).value();
        assertNotNull(itsOwn);
        assertEquals(Map.of("go", BehaviorImplementation.IMPLEMENTED), itsOwn.bodies().states());

        CheckSurface same = reassembled(itsOwn, itsOwn.bodies());
        CheckSurface leftToJava = reassembled(itsOwn, new BehaviorBodies("m",
                Map.of("go", BehaviorImplementation.INJECTION_TARGET)));

        assertEquals(itsOwn, same, "joined from the same parts, the two are one answer");
        assertEquals(itsOwn.module(), leftToJava.module(), "the trees are the same, or this says"
                + " nothing");
        assertNotEquals(itsOwn, leftToJava);
    }

    /** The parts of {@code surface}, joined again beside {@code bodies}. */
    private static CheckSurface reassembled(CheckSurface surface, BehaviorBodies bodies) {
        Map<String, Normalized.Def> normalized = new LinkedHashMap<>();
        for (Normalized.Def each : surface.declarations()) {
            normalized.put(each.name(), each);
        }
        Map<String, Desugared.Fn> desugared = new LinkedHashMap<>();
        for (Desugared.Fn each : surface.desugaredFrom()) {
            desugared.put(each.name(), each);
        }
        return CheckSurface.assemble(surface.settling(), normalized, desugared,
                DeclarationNewtypes.NONE, Map.of(), FakeTables.classify(surface.settling().module()),
                bodies);
    }
}
