package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A test that reads the report of a model is held to that model compiling.
 *
 * <p>A model that does not compile is said nothing of: its report holds no position, no line and
 * no reason. A test asking that nothing of some kind is said, or that everything said is of some
 * kind, passes on that empty report whatever the compiler would say of the model the author meant.
 * So a method that makes a model and reads what is said of it hands the model to
 * {@code ACompiledModel}, which stops the test on an error or says which errors the model is meant
 * to be refused with, and the test cannot pass without that having been done to the model it read.
 * What the rule is, and what it follows, is said at {@link UncheckedModelReports}.
 */
class ATestThatReadsAModelsReportAsksThatTheModelCompilesTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofEverythingCompiledHere();

    private static final String FIXTURES = "souther/architecture/fixture/ModelShapes$";

    /** The shapes written for this check to read, and which of them it refuses. */
    private static final Set<String> REFUSED_SHAPES = new TreeSet<>(List.of(
            "ADerivedModelNeverAsked", "AnotherClassMadeIt", "AnotherModelAsked",
            "AskedOnOneWayOnly", "ErrorsDropped", "ErrorsKept", "FieldNeverAsked",
            "FromACollection", "HandedOnManyTimes", "LeftBeforeTheAsk", "LeftOpenFor",
            "MadeInALambda", "MeasuredThenRead", "ReassignedOnOneWay", "ReplacedAfterTheLook",
            "SwallowedFailure"));

    private static final Set<String> ACCEPTED_SHAPES = new TreeSet<>(List.of(
            "ADerivedModelAsked", "AnotherClassAskedAboutIt", "AskedAfterTheRead",
            "AskedByAMethodOfItsOwn", "AskedOnEveryWay", "AskedThenCaptured", "AskedThenRead",
            "FieldAskedWhereWritten", "HandedIn", "TheErrorsAreWhatWasMeant", "ThroughTheDoor"));

    private static final String HELPER = "souther/compiler/ACompiledModel";

    /**
     * The tests that read a model that cannot be compiled: a chain of declarations too long for
     * the compiler's own stack, and a buffer an editor probe is handed half way through a line.
     */
    private static final Set<String> CANNOT_BE_COMPILED = new TreeSet<>(List.of(
            "souther/compiler/check/ANewtypeChainIsReadOneNameAtATimeTest",
            "souther/compiler/check/AValueAGuaranteeWalkReachesIsOneNodeHoweverFarDownTest$Reading",
            "souther/lsp/analysis/SemanticProbeBenchmark"));

    /** The door the tests of this repository go through. */
    private static final UncheckedModelReports ASKING = new UncheckedModelReports(HELPER);

    /** What the repository's tests do with the models they read, worked out once for the class. */
    private static UncheckedModelReports.Findings findings;

    private static synchronized UncheckedModelReports.Findings findings() {
        if (findings == null) {
            findings = ASKING.of(testClasses());
        }
        return findings;
    }

    private static List<ClassModel> testClasses() {
        List<ClassModel> tests = new ArrayList<>();
        for (Path module : COMPILED.modules()) {
            for (ClassModel each : COMPILED.testClassesOf(module)) {
                if (!each.thisClass().asInternalName().startsWith("souther/architecture/fixture/")) {
                    tests.add(each);
                }
            }
        }
        return tests;
    }

    @Test
    void noTestReadsTheReportOfAModelItWasNotHeldToCompiling() {
        assertEquals(List.of(), new ArrayList<>(findings().refused()),
                "a method reads the report of a model that was not handed to ACompiledModel before"
                        + " the read on every way to it, or after it on every way out, or of a"
                        + " model that cannot be followed to where it was made, so the empty"
                        + " report of a model that did not compile passes it");
    }

    /**
     * And only the tests that cannot compile their model say so.
     *
     * <p>Reading a model without compiling it is the one way past the rule, so it is a list that
     * is closed and read here, and a test that wants to join it is a change to this list that a
     * reviewer sees. What a model on it is too large for is said at the call.
     */
    @Test
    void onlyTheTestsThatCannotCompileTheirModelSayTheyDidNot() {
        Set<String> saying = new TreeSet<>();
        for (ClassModel each : testClasses()) {
            each.methods().forEach(method -> method.code().ifPresent(code -> code.elementList()
                    .stream().filter(InvokeInstruction.class::isInstance)
                    .map(InvokeInstruction.class::cast)
                    .filter(call -> call.owner().asInternalName().equals(HELPER)
                            && call.name().stringValue().equals("notCompiled"))
                    .forEach(call -> saying.add(each.thisClass().asInternalName()))));
        }
        assertEquals(CANNOT_BE_COMPILED, saying,
                "a test reads a model it did not compile, and is not one of those that cannot:"
                        + " a chain of declarations so long that the compiler's own stack"
                        + " overflows on it, and a buffer stopped half way through a line");
    }

    /**
     * And the check turns red on the shapes it is for and on no other.
     *
     * <p>Written as classes of their own and read here, because the repository's tests are held to
     * the rule above and a test that broke it on purpose would be one of them. Each is read with
     * the others, as the tests are, so a model made in one class and read in another is followed.
     */
    @Test
    void itRefusesTheShapesThatPassOnAnEmptyReportAndNoOtherShape() {
        UncheckedModelReports door = new UncheckedModelReports(FIXTURES + "TheDoor");
        List<ClassModel> shapes = new ArrayList<>();
        for (String shape : REFUSED_SHAPES) {
            shapes.add(COMPILED.read(FIXTURES + shape));
        }
        for (String shape : ACCEPTED_SHAPES) {
            shapes.add(COMPILED.read(FIXTURES + shape));
        }
        shapes.add(COMPILED.read(FIXTURES + "Factory"));
        Set<String> refused = new TreeSet<>();
        for (String method : door.of(shapes).refused()) {
            String shape = method.substring(method.indexOf('$') + 1, method.indexOf('#'));
            refused.add(shape);
        }
        assertEquals(REFUSED_SHAPES, refused,
                "a model never asked about, one asked about on only one way to the read or after a"
                        + " return that can come first, one of two asked about when the other was"
                        + " read, one replaced after the look or on one way only, one made in"
                        + " another class or a field or a lambda or a collection, one asked about"
                        + " where the failure is swallowed, and a look at errors() that says"
                        + " nothing are refused; asking through the door before or after the read,"
                        + " on every way, saying what the errors are meant to be, asking in a"
                        + " method of its own, and a model handed in are not");
    }

    /**
     * And the walk finds models made and asked about, which says it reads the tests.
     *
     * <p>Without it a walk over no class would find nothing to refuse and equal the empty list.
     */
    @Test
    void andTheWalkSeesModelsMadeAndAskedAbout() {
        assertTrue(findings().asked() > 0,
                "no test makes a model, asks that it compiles and reads its report, so this walked"
                        + " nothing and would hold either way");
    }
}
