package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.Label;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.BranchInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.classfile.instruction.LabelTarget;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Who makes a {@code LevelRealizer}, because what it has proved is held for as long as it is.
 *
 * <p>The class check of a point and the search of the same point read one proof only when they are
 * asked of one realizer, and a realizer made at either of them would prove it a second time with
 * nothing to tell the two apart: the answers are the same, and so is every test of them. So the
 * methods that make one are held to a list, and a method added to it has to say whose proofs the
 * realizer holds.
 *
 * <p>Read off the compiled classes, so that a realizer made in a helper, or in a class a search
 * object is made of, is found as well as one written on the line a reader would look at. The list
 * is compared whole rather than counted: one site can be dropped and another added without the
 * number moving.
 */
class TheRealizerOfASearchIsMadeWhereItsProofsHaveAnOwnerTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String REALIZER = "souther/compiler/partition/LevelRealizer";

    /**
     * Where one is made, and whose it is.
     *
     * <p>{@code Coverages#searched} makes one for each border its search looks along, handed to the
     * class check and to the search of that border alike. The class check of a measured point makes
     * its own: the measuring and the search of a border are two calls of the pipeline and no owner
     * outlives both, so what it proves is proved again by the search. {@code Adequacy} asks one
     * question and drops the realizer.
     */
    private static final List<String> MAKERS = List.of(
            "souther/compiler/query/Adequacy$Generated#holding("
                    + "Lsouther/compiler/partition/MeasuredInput;"
                    + "Lsouther/compiler/partition/MeasuredInput$Lines;Ljava/util/List;"
                    + "Lsouther/compiler/partition/ReachingCuts;"
                    + "Lsouther/compiler/coverage/ControlPlace$Outcome;)"
                    + "Lsouther/compiler/partition/HeldOutcome$Bringing;",
            "souther/compiler/query/Coverages#searched("
                    + "Lsouther/compiler/query/LineReadings;"
                    + "Lsouther/compiler/partition/MeasuredInput;"
                    + "Lsouther/compiler/query/Coverages$Probe;"
                    + "Lsouther/compiler/partition/ReachingCuts;)"
                    + "Lsouther/compiler/query/LineReadings;",
            "souther/compiler/query/Coverages$1#classLiesOutsideTheCase("
                    + "Lsouther/compiler/partition/Criterion;)Z");

    @Test
    void theseAreTheOnlyMethodsThatMakeOne() {
        assertEquals(MAKERS, makers().stream().map(Maker::method).sorted().toList(),
                "a realizer made where a proof is asked for is one that proves it again; make it"
                        + " where the search it serves begins, and add the method here with whose"
                        + " it is");
    }

    /**
     * And a search makes its realizer for the border and not before the borders.
     *
     * <p>One made ahead of them would hold the regions of every border to the last. Two borders do
     * reach one region now and then, and each proves what it is asked of it; that is given up so
     * that a border's regions are let go with it. Read as the realizer being made inside a loop of
     * the method, which is the span between a jump back and the place it jumps to.
     */
    @Test
    void aSearchMakesItsRealizerInsideTheLoopOverItsBorders() {
        Maker searching = makers().stream()
                .filter(each -> each.method().startsWith("souther/compiler/query/Coverages#searched("))
                .findFirst().orElseThrow(() -> new AssertionError("the search no longer makes one"));
        assertTrue(searching.insideALoop(),
                "a realizer made before the loop over the borders outlives each of them");
    }

    /** A call of the constructor, where it is, and whether a jump back spans it. */
    private record Maker(String method, boolean insideALoop) {}

    private static List<Maker> makers() {
        List<Maker> out = new ArrayList<>();
        for (ClassModel owner : COMPILED.classesOf(COMPILED.module("souther-compiler"))) {
            for (MethodModel method : owner.methods()) {
                for (CodeModel code : method.code().stream().toList()) {
                    List<CodeElement> elements = code.elementList();
                    Map<Label, Integer> placed = new HashMap<>();
                    List<int[]> loops = new ArrayList<>();
                    for (int at = 0; at < elements.size(); at++) {
                        if (elements.get(at) instanceof LabelTarget target) {
                            placed.put(target.label(), at);
                        } else if (elements.get(at) instanceof BranchInstruction jump
                                && placed.containsKey(jump.target())) {
                            loops.add(new int[] {placed.get(jump.target()), at});
                        }
                    }
                    for (int at = 0; at < elements.size(); at++) {
                        if (elements.get(at) instanceof InvokeInstruction invoke
                                && invoke.owner().asInternalName().equals(REALIZER)
                                && invoke.name().stringValue().equals("<init>")) {
                            int made = at;
                            out.add(new Maker(AMethod.of(owner, method),
                                    loops.stream().anyMatch(span -> span[0] < made && made < span[1])));
                        }
                    }
                }
            }
        }
        return out;
    }
}
