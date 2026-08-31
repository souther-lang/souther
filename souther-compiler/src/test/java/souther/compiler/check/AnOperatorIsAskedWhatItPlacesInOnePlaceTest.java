package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Who reads an operator for what it places, which is what keeps a recognised comparison recognised.
 *
 * <p>A reader below the point where a binary was recognised as a comparison holds
 * {@link ComparisonClaim}, which has no case for an operator that places nothing. That stands only
 * while nothing down there goes back to the operator: one call to {@link ComparisonPlacement#of}
 * hands back the wide answer, and whoever made it has a case to invent an answer for again — which
 * is how six readings came to answer for a comparison that was never one.
 *
 * <p>So the readers of the wide answer are named here. Outside the classification itself they are
 * the two boundaries this arrangement has: {@link Comparison} refines a node into a comparison, and
 * {@link souther.compiler.inputs.ComparedNumber} reads any binary a walk met, where an operator
 * that places nothing is a thing that really arrives. Beside them is the boolean spelling of the
 * same answer, which is in the classification and asked in one place of its own.
 *
 * <p>Read off the compiled classes, because what a method calls is what the class file says. A
 * reading of the sources would answer the same question a second way, and would not see a call
 * written inside a lambda as the method that holds it.
 */
class AnOperatorIsAskedWhatItPlacesInOnePlaceTest {

    private static final String PLACEMENT = "souther/compiler/check/ComparisonPlacement";

    /** Who may read an operator for what it places, and why. */
    private static final Map<String, String> MAY_ASK = asking();

    private static Map<String, String> asking() {
        Map<String, String> may = new LinkedHashMap<>();
        may.put("souther.compiler.check.Comparison.of",
                "the one place a node becomes a comparison, which is what carries the claim to"
                        + " every reader below it");
        may.put("souther.compiler.check.ComparisonPlacement.orders",
                "the same answer asked as a boolean, for a reader that holds an operator and no"
                        + " comparison");
        may.put("souther.compiler.inputs.ComparedNumber.of",
                "reads any binary a walk met, so an operator that places nothing arrives here and"
                        + " is answered rather than excluded");
        return may;
    }

    /** Who may ask whether an operator orders its values, which is the wide answer read as a
     *  boolean. The reading of an invariant's clauses is the one left, and it is where the same
     *  arrangement is still to be made. */
    private static final Map<String, String> MAY_ASK_ORDERS = Map.of(
            "souther.compiler.check.InvariantBound.ordering",
            "a clause of a data is read off the syntax tree and has no recognised comparison to"
                    + " carry a claim");

    @Test
    void onlyTheTwoBoundariesReadAnOperatorForWhatItPlaces() throws IOException {
        assertEquals(new TreeSet<>(MAY_ASK.keySet()), callersOf("of"),
                "a reader below a recognised comparison that asks the operator again holds the"
                        + " wide answer, and has a case to invent an answer for. Each of the two"
                        + " that may is here with why: " + MAY_ASK);
    }

    @Test
    void whetherAnOperatorOrdersIsAskedOnlyWhereNoComparisonIsHeld() throws IOException {
        assertEquals(new TreeSet<>(MAY_ASK_ORDERS.keySet()), callersOf("orders"),
                "asked as a boolean, what an operator places is left behind at the test. Where"
                        + " that is still done is here with why: " + MAY_ASK_ORDERS);
    }

    /** Every method of the compiler that calls {@code ComparisonPlacement.<name>}. */
    private static TreeSet<String> callersOf(String name) throws IOException {
        TreeSet<String> callers = new TreeSet<>();
        int read = 0;
        for (Path each : classes()) {
            ClassModel model = ClassFile.of().parse(Files.readAllBytes(each));
            read++;
            String owner = model.thisClass().asInternalName().replace('/', '.').replace('$', '.');
            for (MethodModel method : model.methods()) {
                method.code().ifPresent(code -> code.forEach(element -> {
                    if (element instanceof InvokeInstruction call
                            && call.owner().asInternalName().equals(PLACEMENT)
                            && call.name().stringValue().equals(name)) {
                        callers.add(owner + "." + method.methodName().stringValue());
                    }
                }));
            }
        }
        assertFalse(read == 0, "no compiled class was read at all, so this says nothing");
        return callers;
    }

    private static List<Path> classes() throws IOException {
        Path root = Path.of("target", "classes").toAbsolutePath();
        try (Stream<Path> walk = Files.walk(root)) {
            return new ArrayList<>(walk.filter(p -> p.toString().endsWith(".class")).toList());
        }
    }
}
