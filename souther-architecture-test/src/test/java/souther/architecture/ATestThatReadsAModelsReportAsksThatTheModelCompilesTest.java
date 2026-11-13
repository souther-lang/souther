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
            "AskedOnOneWayOnly", "ChangedThenFailedAndCaught", "ChangedThroughAMethod",
            "ChangedThroughTheDb", "DbChangedThroughAVariable", "DbHandedToAMethod",
            "EngineHandsItIn", "ErrorsDropped", "ErrorsKept", "FieldMutatedAfterTheLook",
            "FieldNeverAsked", "FromACollection", "HandedOnManyTimes",
            "HandedToCodeThatChangesIt", "LambdaMadeNotRun", "LeftBeforeTheAsk",
            "LeftOpenFor", "MadeInALambda", "MeasuredThenRead", "MutatedAfterTheLook",
            "NotCompiledButReportRead", "NotCompiledOffTheList", "NotCompiledReadsAllReports",
            "ParameterNobodyPasses", "ReadThenChangedThenAsked",
            "ReadThenChangedThenAskedInAMethod", "ReassignedOnOneWay", "ReplacedAfterTheLook",
            "SwallowedFailure", "UpdatedAfterTheLook", "WarningsOfAnUnaskedModel"));

    private static final Set<String> ACCEPTED_SHAPES = new TreeSet<>(List.of(
            "ADerivedModelAsked", "AliasOfAnAskedModel", "AnotherClassAskedAboutIt",
            "AskedAfterTheRead", "AskedByAMethodOfItsOwn", "AskedOnEveryWay", "AskedThenCaptured",
            "AskedThenRead", "ConfiguredThroughTheDbBeforeTheLook", "DbHandedToAReader",
            "FieldAskedWhereWritten", "HelperThatChangesAndAsks", "MarkedAndNotRun",
            "NotCompiledOnTheList",
            "ParameterHandedByACaller", "TheErrorsAreWhatWasMeant", "ThroughTheDoor",
            "UpdatedThenAsked"));

    private static final String HELPER = "souther/compiler/ACompiledModel";

    /**
     * The methods that read a model they did not compile, and say so: a chain of declarations too
     * long for the compiler's own stack, and a buffer an editor probe is handed half way through a
     * line. The one way past the rule, so it is a list that is closed, and a method that wants to
     * join it is a change to this list that a reviewer sees. What a model on it cannot be compiled
     * for is said at the call.
     */
    private static final Set<String> CANNOT_BE_COMPILED = Set.of(
            AMethod.of("souther/compiler/check/ANewtypeChainIsReadOneNameAtATimeTest", "rules",
                    "(I)Lsouther/compiler/check/RuleReadingSource;"),
            AMethod.of("souther/compiler/check/"
                            + "AValueAGuaranteeWalkReachesIsOneNodeHoweverFarDownTest$Reading",
                    "<init>", "(Ljava/lang/String;)V"),
            AMethod.of("souther/lsp/analysis/SemanticProbeBenchmark", "through",
                    "(Lsouther/lsp/analysis/SemanticProbe;Ljava/util/Map;Ljava/lang/String;"
                            + "Ljava/lang/String;I)V"));

    /** The door the tests of this repository go through. */
    private static final UncheckedModelReports ASKING =
            new UncheckedModelReports(HELPER, CANNOT_BE_COMPILED);

    /** What the repository's tests do with the models they read, worked out once for the class. */
    private static UncheckedModelReports.Findings findings;

    private static synchronized UncheckedModelReports.Findings findings() {
        if (findings == null) {
            List<ClassModel> tests = new ArrayList<>();
            List<ClassModel> production = new ArrayList<>();
            for (Path module : COMPILED.modules()) {
                production.addAll(COMPILED.classesOf(module));
                for (ClassModel each : COMPILED.testClassesOf(module)) {
                    if (!each.thisClass().asInternalName()
                            .startsWith("souther/architecture/fixture/")) {
                        tests.add(each);
                    }
                }
            }
            findings = ASKING.of(tests, production);
        }
        return findings;
    }

    @Test
    void noTestReadsTheReportOfAModelItWasNotHeldToCompiling() {
        assertEquals(List.of(), new ArrayList<>(findings().refused()),
                "a method reads the report of a model that was not handed to ACompiledModel before"
                        + " the read on every way to it, or after it on every way out, or of a"
                        + " model that cannot be followed to where it was made, or that nothing"
                        + " hands it, or says it did not compile it and is not on the list that may,"
                        + " so the empty report of a model that did not compile passes it");
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
        UncheckedModelReports door = new UncheckedModelReports(FIXTURES + "TheDoor", Set.of(
                AMethod.of(FIXTURES + "NotCompiledOnTheList", "read", "(Ljava/lang/String;)Z"),
                AMethod.of(FIXTURES + "NotCompiledButReportRead", "read",
                        "(Ljava/lang/String;)Lsouther/compiler/report/AdequacyReport;"),
                AMethod.of(FIXTURES + "NotCompiledReadsAllReports", "read",
                        "(Ljava/lang/String;)Z")));
        List<ClassModel> shapes = new ArrayList<>();
        for (String shape : REFUSED_SHAPES) {
            shapes.add(COMPILED.read(FIXTURES + shape));
        }
        for (String shape : ACCEPTED_SHAPES) {
            shapes.add(COMPILED.read(FIXTURES + shape));
        }
        shapes.add(COMPILED.read(FIXTURES + "Factory"));
        Set<String> refused = new TreeSet<>();
        List<ClassModel> production = List.of(COMPILED.read(FIXTURES + "ProductionChanger"));
        for (String method : door.of(shapes, production).refused()) {
            refused.add(method.substring(method.indexOf('$') + 1, method.indexOf('#')));
        }
        assertEquals(REFUSED_SHAPES, refused,
                "a model never asked about, one asked about on only one way to the read or after a"
                        + " return that can come first, one of two asked about when the other was"
                        + " read, one replaced after the look or on one way only, one changed"
                        + " after it was asked about, one asked about by a lambda that was made"
                        + " and not run, one made in another class or a field or a lambda or a"
                        + " collection, one asked about where the failure is swallowed, one"
                        + " whose warnings are read, one read without compiling it where that is"
                        + " not allowed, one that nothing hands in, and a look at errors() that"
                        + " says nothing are refused; asking through the door before or after the"
                        + " read, on every way, through a copy of the variable, saying what the"
                        + " errors are meant to be, asking in a method of its own, and a model"
                        + " handed in by a caller that asked are not");
    }

    /**
     * And what a model and its store can do is each said to read, to change or to do neither.
     *
     * <p>The check proves a read only of what it follows, so a method added to either class is
     * one it does not know to be a change until it is said here.
     */
    @Test
    void everyMethodOfAModelAndItsStoreIsSaidToReadChangeOrNeither() {
        assertEquals(Set.of(), ModelVocabulary.unsaid(
                        COMPILED.read(ModelVocabulary.COMPILATION),
                        COMPILED.read(ModelVocabulary.DB)),
                "a method of Compilation or Db is not said in ModelVocabulary to read what a model"
                        + " says, to change what it is, or to do neither");
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
