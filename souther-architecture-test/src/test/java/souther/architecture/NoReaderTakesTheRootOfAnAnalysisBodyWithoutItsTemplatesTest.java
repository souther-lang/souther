package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.Map;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Who takes the root tree of an analysis body, and says what it does about the values it builds.
 *
 * <p>The body an analysis reads holds where a value is built and not what it means, which is in its
 * templates. A reader that takes the root and walks it meets a build as a leaf, and reads a body
 * with every value's meaning missing — with nothing failing, since a leaf is a well-formed node. So
 * taking the root is a decision, and this is the list of who has made it and what each of them does
 * about the templates.
 *
 * <p>The class and not the method: what a reader does about the templates is a fact about the
 * reader. A caller that is not here is one that has not said, and it says so here before it takes
 * the root.
 */
class NoReaderTakesTheRootOfAnAnalysisBodyWithoutItsTemplatesTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String THE_ROOT = "souther/compiler/check/AnalysisBody#core";

    /** Who takes the root, and what it does about the templates beside it. */
    private static final Map<String, String> TAKES_THE_ROOT = Map.of(
            "souther/compiler/check/ElementBindings",
            "reads the bindings of the root and of every template, and holds what a name given a"
                    + " build is",
            "souther/compiler/partition/ComparisonReadings",
            "reads the root, and then each template once under what every build of it has in common",
            "souther/compiler/partition/PredicateReadings",
            "reads the root, and then each template once, live where any build of it is",
            "souther/compiler/partition/DecisionReading",
            "reads the root, and answers a build by what its template does; what is inside a template"
                    + " is no way of the body, since a value takes no input");

    @Test
    void everyReaderThatTakesTheRootHasSaidWhatItDoesAboutTheTemplates() {
        TreeSet<String> takers = new TreeSet<>();
        for (ClassModel each : COMPILED.all()) {
            String caller = each.thisClass().asInternalName();
            if (caller.equals("souther/compiler/check/AnalysisBody")) {
                continue;
            }
            for (MethodModel method : each.methods()) {
                method.code().ifPresent(code -> {
                    for (CodeElement element : code) {
                        if (element instanceof InvokeInstruction invoked
                                && (invoked.owner().name().stringValue() + "#"
                                        + invoked.name().stringValue()).equals(THE_ROOT)) {
                            takers.add(caller);
                        }
                    }
                });
            }
        }

        assertEquals(new TreeSet<>(TAKES_THE_ROOT.keySet()), takers,
                "a reader that takes the root of an analysis body is one that has said what it does"
                        + " about the values the body builds: " + TAKES_THE_ROOT);
    }
}
