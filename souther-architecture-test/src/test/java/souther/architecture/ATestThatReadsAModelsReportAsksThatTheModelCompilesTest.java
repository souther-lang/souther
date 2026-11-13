package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A test that reads the report of a model asks that the model compiles.
 *
 * <p>A model that does not compile is said nothing of: its report holds no position, no line and
 * no reason. A test asking that nothing of some kind is said, or that everything said is of some
 * kind, passes on that empty report whatever the compiler would say of the model the author meant.
 * So a method that compiles a source and reads what is said of it hands the model to
 * {@code ACompiledModel} first, which stops the test on an error, or says which errors the model
 * is meant to be refused with. What the rule is, and what it cannot see, is said at
 * {@link UncheckedModelReports}.
 */
class ATestThatReadsAModelsReportAsksThatTheModelCompilesTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofEverythingCompiledHere();

    private static final String FIXTURES = "souther/architecture/fixture/ModelShapes$";

    private static final List<String> SHAPES = List.of("LeftOpenFor", "MeasuredThenRead",
            "ErrorsDropped", "ErrorsKept", "LeftBeforeTheAsk", "AskedAfterTheRead",
            "AnotherModelAsked", "ADerivedModelNeverAsked", "ADerivedModelAsked",
            "ReplacedAfterTheLook", "AskedOnOneWayOnly", "ThroughTheDoor", "AskedThenRead",
            "TheErrorsAreWhatWasMeant", "AskedByAMethodOfItsOwn", "HandedIn");

    /** The door the tests of this repository go through. */
    private static final UncheckedModelReports ASKING =
            new UncheckedModelReports("souther/compiler/ACompiledModel");

    @Test
    void noTestReadsTheReportOfAModelItNeverAskedCompiles() {
        assertEquals(List.of(), new ArrayList<>(ASKING.in(testClasses())),
                "a method reads the report of a model that was not handed to ACompiledModel first,"
                        + " so the empty report of a model that did not compile passes it");
    }

    /**
     * And no test reads a report of a model the walk cannot follow to where it was made.
     *
     * <p>A model that reaches a read by a branch, or by an operation that is not a plain load, is
     * a read the rule above does not see. That is changed in the test, so that the rule has
     * nowhere to be blind.
     */
    @Test
    void noTestReadsTheReportOfAModelTheCheckCannotFollow() {
        assertEquals(List.of(), new ArrayList<>(ASKING.unresolved(testClasses())),
                "a method reads a report of a model that the check cannot follow from where it was"
                        + " made: it holds the model in a local variable, and asks about it before"
                        + " the read");
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

    /**
     * And the check turns red on the shapes it is for and on no other.
     *
     * <p>Written as classes of their own and read here, because the repository's tests are held to
     * the rule above and a test that broke it on purpose would be one of them.
     */
    @Test
    void itRefusesTheShapesThatPassOnAnEmptyReportAndNoOtherShape() {
        UncheckedModelReports door = new UncheckedModelReports(FIXTURES + "TheDoor");
        Set<String> refused = new TreeSet<>();
        for (String shape : SHAPES) {
            for (String method : door.in(List.of(COMPILED.read(FIXTURES + shape)))) {
                refused.add(method.substring(method.indexOf('$') + 1));
            }
        }
        assertEquals(List.of(
                        "ADerivedModelNeverAsked#read(Ljava/lang/String;)"
                                + "Lsouther/compiler/report/AdequacyReport;",
                        "AnotherModelAsked#read(Ljava/lang/String;Ljava/lang/String;)"
                                + "Lsouther/compiler/report/AdequacyReport;",
                        "AskedOnOneWayOnly#read(Ljava/lang/String;Z)"
                                + "Lsouther/compiler/report/AdequacyReport;",
                        "ErrorsDropped#read(Ljava/lang/String;)"
                                + "Lsouther/compiler/report/AdequacyReport;",
                        "ErrorsKept#read(Ljava/lang/String;)"
                                + "Lsouther/compiler/report/AdequacyReport;",
                        "LeftBeforeTheAsk#read(Ljava/lang/String;)"
                                + "Lsouther/compiler/report/AdequacyReport;",
                        "LeftOpenFor#read(Ljava/lang/String;)"
                                + "Lsouther/compiler/report/AdequacyReport;",
                        "MeasuredThenRead#read(Ljava/lang/String;)"
                                + "Lsouther/compiler/report/AdequacyReport;",
                        "ReplacedAfterTheLook#read(Ljava/lang/String;Ljava/lang/String;)"
                                + "Lsouther/compiler/report/AdequacyReport;"),
                new ArrayList<>(refused),
                "a model never asked about, one asked about on only one way to the read or after a"
                        + " return that can come first, one of two asked about when the other was"
                        + " read, one replaced after the look, and a look at errors() that says"
                        + " nothing are refused; asking through the door before or after the read,"
                        + " saying what the errors are meant to be, asking in a method of its own,"
                        + " and a model handed in are not");
        assertEquals(Set.of(), door.unresolved(shapes()), "every shape is one the walk can follow");
    }

    private static List<ClassModel> shapes() {
        return SHAPES.stream().map(shape -> COMPILED.read(FIXTURES + shape)).toList();
    }

    /**
     * And the walk finds models made and asked about, which says it reads the tests.
     *
     * <p>Without it a walk over no class would find nothing to refuse and equal the empty list.
     */
    @Test
    void andTheWalkSeesModelsMadeAndAskedAbout() {
        List<ClassModel> tests = new ArrayList<>();
        for (Path module : COMPILED.modules()) {
            tests.addAll(COMPILED.testClassesOf(module));
        }
        assertTrue(ASKING.asking(tests) > 0,
                "no test makes a model, asks that it compiles and reads its report, so this walked"
                        + " nothing and would hold either way");
    }
}
