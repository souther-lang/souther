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
    private static final Map<String, String> TAKES_THE_ROOT = Map.ofEntries(
            Map.entry("souther/compiler/check/ElementBindings",
                    "reads the bindings of the root and of every template, and holds what a name"
                            + " given a build is"),
            Map.entry("souther/compiler/partition/ComparisonReadings",
                    "reads the root, and then each template once under what every build of it has"
                            + " in common"),
            Map.entry("souther/compiler/partition/PredicateReadings",
                    "reads the root, and then each template once, live where any build of it is"),
            Map.entry("souther/compiler/partition/MeaningsOfABodyReading",
                    "reads the root alone: it files what a condition states for a reader of the"
                            + " tree that runs, and that tree builds a value by calling it, so no"
                            + " condition such a reader asks is inside a template"),
            Map.entry("souther/compiler/partition/GuardThresholds",
                    "asks whether working the root out ends a run, and of each build met what its"
                            + " definition does; a build with no definition held is not shown to"
                            + " end none"),
            Map.entry("souther/compiler/partition/StopPastTheRepresentation",
                    "reads the root, and then each template once: an operation a build works out"
                            + " stops a run where the value is built as one the root works out"
                            + " does"),
            Map.entry("souther/compiler/partition/DecisionReading",
                    "reads the root, and answers a build by what its template does; what is inside"
                            + " a template is no way of the body, since a value takes no input"),
            Map.entry("souther/compiler/reading/KeptElements",
                    "reads the root alone: it looks for a call of the behavior's own body, and the"
                            + " tree that runs builds a value by calling it, so a call whose"
                            + " expansion is met there is never one inside a template"),
            Map.entry("souther/compiler/query/CallExampleSeeds",
                    "reads the root alone: it looks for the calls the body makes of other"
                            + " behaviors, and a call inside a template is not looked for, so it"
                            + " seeds no row"),
            Map.entry("souther/compiler/query/CalledBehaviors",
                    "reads the root alone, as CallExampleSeeds does so that the two never disagree"
                            + " about what a body calls: a call inside a template is not looked"
                            + " for, so the behavior it calls is not one the body is handed rows of"
                            + " first"),
            Map.entry("souther/compiler/query/Adequacy$BodyAtACall",
                    "hands the root on to the reading of a call that enters the body, with the"
                            + " bindings of the root and of every template, so a name a build gives"
                            + " is what it holds there too"));

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
