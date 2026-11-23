package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Whether a run of a row gets past what a body works out is asked of one owner,
 * {@code check/ARowsRun}, which takes the premises a row's run is read under: an
 * {@code unreachable} is gotten past, a call of a behavior is gotten past where that behavior's rows
 * get past its body, and an operation that ends a run only past the representation is gotten past.
 *
 * <p>{@code WhatARunMayEndFor} says what a run may end for, over every run, and stands for the
 * readers whose question is about real runs. Its walks over a tree, and what the behaviors called
 * answer, are asked by the classes below and no others, each for the reason written beside it. A
 * reader of a body's rows that walks the tree with the owner of real runs instead leaves a body
 * open on an {@code unreachable} or a call the rows get past, which is the defect this holds off.
 */
class WhatARowsRunGetsPastIsAskedOfOneOwnerTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String C = "souther/compiler/";

    /** The walks of {@code WhatARunMayEndFor} that go down a tree, which a reader of a row's run
     *  would otherwise use in place of the owner's. */
    private static final Set<String> WALKS = Set.of("of", "endsNoneBeneath",
            "endsNoneBeneathApart");

    @Test
    void theWalksOverATreeOfWhatEveryRunMayEndForAreAskedOnlyWhereTheQuestionIsAboutEveryRun() {
        assertEquals(List.of(
                        // A clause of a declaration, where an unreachable is refused and what is
                        // read is whether working the clause out stops, not a row's run.
                        C + "check/ContainerCounts",
                        // Which inputs are rows at all: a run that ends is no row, whatever it
                        // ended for, so the order a walk meets its elements in decides it.
                        C + "check/OrderOfElements",
                        // Whether a path completes, which an unreachable is the model saying it
                        // does not.
                        C + "check/PathCompletion",
                        // A clause of a declaration, as above.
                        C + "check/SidesBalanced",
                        // The owner itself.
                        C + "check/WhatARunMayEndFor",
                        // Whether a witness is sought: the run of a row being built reaches the
                        // comparison only where nothing before it stops, an unreachable included.
                        C + "partition/WhatARunWorksOutBeforeACount",
                        // The clauses of a construction's invariant, as above: whether one is
                        // refused is whether its clauses, worked out, stop.
                        C + "partition/WorkedOutToReachIt"),
                calling(C + "check/WhatARunMayEndFor", WALKS),
                "a reader of what a row's run gets past asks check/ARowsRun, which takes the"
                        + " premises such a run is read under; one added here is said beside the"
                        + " others with the question it asks about every run");
    }

    @Test
    void whatTheBehaviorsCalledAnswerOfTheirRowsIsAskedOnlyByTheOwner() {
        assertEquals(List.of(C + "check/ARowsRun"),
                calling(C + "check/BehaviorAnswers", Set.of("rowsRunsGetPast")),
                "that a call is gotten past where the behavior's rows get past its body is one of"
                        + " the premises of a row's run, taken in one place");
    }

    /** The classes whose code calls one of {@code names} on {@code owner}, other than it. */
    private static List<String> calling(String owner, Set<String> names) {
        TreeSet<String> out = new TreeSet<>();
        for (ClassModel each : COMPILED.classesOf(COMPILED.module("souther-compiler"))) {
            for (MethodModel method : each.methods()) {
                for (CodeModel code : method.code().stream().toList()) {
                    for (CodeElement element : code) {
                        if (element instanceof InvokeInstruction invoke
                                && invoke.owner().asInternalName().equals(owner)
                                && names.contains(invoke.name().stringValue())) {
                            out.add(each.thisClass().asInternalName());
                        }
                    }
                }
            }
        }
        return List.copyOf(out);
    }
}
