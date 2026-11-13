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
 * So a method that compiles a source and reads what is said of it goes through
 * {@code ACompiledModel}, which stops the test on an error, or looks at {@code errors()} and uses
 * what it saw. A test that means the model not to compile reads its errors, and that is the look.
 * What the rule is, and what it cannot see, is said at {@link UncheckedModelReports}.
 */
class ATestThatReadsAModelsReportAsksThatTheModelCompilesTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofEverythingCompiledHere();

    private static final String FIXTURES = "souther/architecture/fixture/ModelShapes$";

    /** The door the tests of this repository go through. */
    private static final UncheckedModelReports ASKING =
            new UncheckedModelReports("souther/compiler/ACompiledModel");

    @Test
    void noTestReadsTheReportOfAModelItNeverAskedCompiles() {
        List<ClassModel> tests = new ArrayList<>();
        for (Path module : COMPILED.modules()) {
            for (ClassModel each : COMPILED.testClassesOf(module)) {
                if (!each.thisClass().asInternalName().startsWith("souther/architecture/fixture/")) {
                    tests.add(each);
                }
            }
        }
        assertEquals(List.of(), new ArrayList<>(ASKING.in(tests)),
                "a method reads the report of a model it never asked compiles, so the empty report"
                        + " of a model that did not compile passes it: it starts from"
                        + " ACompiledModel, or it reads errors() of the model and uses what it saw");
    }

    /**
     * And the check turns red on the shapes it is for and on no other.
     *
     * <p>Written as classes of their own and read here, because the repository's tests are held to
     * the rule above and a test that broke it on purpose would be one of them.
     */
    @Test
    void itRefusesTheShapesThatPassOnAnEmptyReportAndNoOtherShape() {
        UncheckedModelReports door = new UncheckedModelReports(FIXTURES + "TheStopOnAnError");
        Set<String> refused = new TreeSet<>();
        for (String shape : List.of("LeftOpenFor", "MeasuredThenRead", "ErrorsDropped",
                "ThroughTheDoor", "TheErrorsAreWhatWasMeant", "AnEmptyReportThatIsTheAnswer")) {
            ClassModel model = COMPILED.read(FIXTURES + shape);
            for (String method : door.in(List.of(model))) {
                refused.add(method.substring(method.indexOf('$') + 1));
            }
        }
        assertEquals(List.of(
                        "ErrorsDropped#read(Ljava/lang/String;)Lsouther/compiler/report/AdequacyReport;",
                        "LeftOpenFor#read(Ljava/lang/String;)Lsouther/compiler/report/AdequacyReport;",
                        "MeasuredThenRead#read(Ljava/lang/String;)Lsouther/compiler/report/AdequacyReport;"),
                new ArrayList<>(refused),
                "the shapes with no look at the model, a look that is dropped, and a model read in"
                        + " a method other than the one that made it are refused; a look through the"
                        + " door, a look compared with what was meant, and a look before an empty"
                        + " answer are not");
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
