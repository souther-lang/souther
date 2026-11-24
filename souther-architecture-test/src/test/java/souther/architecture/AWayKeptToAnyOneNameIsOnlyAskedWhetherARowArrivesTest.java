package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.List;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Who makes a way by keeping the first name it meets for each element of a container.
 *
 * <p>Such a way says less than the rows that arrive do, which is all a question of whether a row
 * arrives asks of it. A point, a class or a premise of one element composed with it is composed
 * with a region kept to another element's name, and what comes of that is a point refuted for no
 * reason. A way that something is composed against is kept to the elements the border reads, by
 * whoever has the border ({@code ElementsOnTheWay.keptToOneElementEach}), and is made as it
 * comes.
 *
 * <p>So the methods that may make one the other way are held to a list, and a method added to it
 * has to say that it only asks whether a row arrives. By method and not by class, since a class
 * that asks whether a row arrives may also hold the reader a point is composed against. Read off
 * the compiled classes, and compared whole.
 */
class AWayKeptToAnyOneNameIsOnlyAskedWhetherARowArrivesTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String WAY = "souther/compiler/partition/WayToTheBorder";

    /**
     * Where one is made, and what is asked of it.
     *
     * <p>{@code ReachingCuts#held} asks what a condition coming out one way takes of a row, and
     * {@code #neverTogether} whether two ways can hold together; {@code HeldOutcome#along} and
     * {@code Reachability#readAs} read ways out of the accounts of those;
     * {@code ComparisonReadings#mayEvaluate} and {@code WayThroughAClause#mayReachTheNext} ask
     * whether the next statement may be reached; {@code DecisionNaming#noInputTakes} asks whether
     * any input takes a path; and {@code DecisionReading#states} and {@code #statesToACase} state
     * the way a rule is reached on, which is read for whether a row arrives and as a region a row
     * for a case is looked for in, wider than the rows that arrive and never narrower.
     *
     * <p>{@code ReachingCuts#wayTo} and {@code #wayToTheComparison} are not here: what a point is
     * composed against is the way kept to the elements the line reads.
     */
    private static final List<String> MAKERS = List.of(
            "souther/compiler/partition/ComparisonReadings#mayEvaluate",
            "souther/compiler/partition/DecisionNaming#noInputTakes",
            "souther/compiler/partition/DecisionReading#states",
            "souther/compiler/partition/DecisionReading#statesToACase",
            "souther/compiler/partition/HeldOutcome#along",
            "souther/compiler/partition/Reachability#readAs",
            "souther/compiler/partition/ReachingCuts#held",
            "souther/compiler/partition/ReachingCuts#neverTogether",
            "souther/compiler/partition/WayThroughAClause#mayReachTheNext");

    /** The method a call is written in, by its class and name: a lambda or a nested class is
     *  taken as the method it is written inside. */
    private static String methodOf(ClassModel owner, MethodModel method) {
        String in = owner.thisClass().asInternalName();
        String name = method.methodName().stringValue();
        if (name.startsWith("lambda$")) {
            name = name.substring("lambda$".length(), name.lastIndexOf('$'));
        }
        return (in.contains("$") ? in.substring(0, in.indexOf('$')) : in) + "#" + name;
    }

    @Test
    void theseAreTheOnlyMethodsThatMakeOne() {
        TreeSet<String> making = new TreeSet<>();
        for (ClassModel owner : COMPILED.classesOf(COMPILED.module("souther-compiler"))) {
            for (MethodModel method : owner.methods()) {
                for (CodeModel code : method.code().stream().toList()) {
                    for (CodeElement element : code.elementList()) {
                        if (element instanceof InvokeInstruction invoke
                                && invoke.owner().asInternalName().equals(WAY)
                                && invoke.name().stringValue().equals("forArrival")) {
                            making.add(methodOf(owner, method));
                        }
                    }
                }
            }
        }
        assertEquals(MAKERS, List.copyOf(making),
                "a way kept to any one name says less than the rows that arrive do; where a point,"
                        + " a class or a premise is composed against a way, keep it to the border's"
                        + " names, and where only arrival is asked add the method here");
    }
}
