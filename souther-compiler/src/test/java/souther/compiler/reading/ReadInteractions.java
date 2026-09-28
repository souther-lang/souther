package souther.compiler.reading;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertNotNull;

/** What the coverage reading of one behavior of a one-module source groups into interactions. */
final class ReadInteractions {

    private ReadInteractions() {
    }

    /** The interactions the reading finds in {@code behavior} of {@code source}. */
    static List<Interaction> read(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get(behavior);
        assertNotNull(body, "the behavior under test has a body");
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get(behavior);
        return CoverageRead.of(behavior, body, checked.plan(), inputs, rules).interactions();
    }

    /** The sizes of each group's factors, which is the shape of the space a row is owed for. */
    static List<List<Integer>> shape(List<Interaction> found) {
        return found.stream()
                .map(group -> group.factors().stream().map(f -> f.outcomes().size()).toList())
                .toList();
    }

    /** What each group's way in is made of, said by the kind of condition each decision is. */
    static List<List<String>> reachKinds(List<Interaction> found) {
        return found.stream()
                .map(group -> group.reach().stream()
                        .map(decision -> decision.constrains().getClass().getSimpleName())
                        .toList())
                .toList();
    }
}
