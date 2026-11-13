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
            "ADerivedModelNeverAsked", "AllReportsOfAnAnswered", "AnotherClassMadeIt",
            "AnotherModelAsked", "AnswerWarningsOnly", "AskedAliasOfAFieldChangedByAMethod",
            "AnswerKeptInAVariable", "AskedOnOneWayOnly", "BoundMethodRefChanges",
            "BoundMethodRefReads", "BoxedInAnArray", "ChangedThroughTheParentNotTheDefault",
            "ChoosesBetweenAStoreItMadeAndTheOneGiven",
            "ConditionalModelJoin", "DbHeldHandedToAConsumer",
            "ChangedOnTheWayThatFails",
            "ChangedThenFailedAndCaught", "ChangedThroughADefaultMethod",
            "ChangedThroughAGenericFunction", "ChangedThroughAGetter", "ChangedThroughAHolder",
            "ChangedThroughAMethod", "ChangedThroughAnAnonymousClass",
            "ChangedThroughAnInheritedMethod", "ChangedThroughAnInterface",
            "ChangedThroughTheDb", "CopyHandedToAConsumer", "DbChangedThroughAVariable",
            "DbHandedToAMethod", "DbKeptInAFieldThenChanged",
            "DiagnosticsAreNotACompileCheck", "DiagnosticsOfAModelNobodyAsked",
            "EngineHandsItIn", "ErrorsDropped", "ErrorsKept",
            "FieldChangedByTheVariableItCameIn", "FieldChangedByTheVariableItWasReadInto",
            "FieldHandedToAConsumer", "FieldMutatedAfterTheLook",
            "FieldNeverAsked", "FromACollection", "HandedOnManyTimes",
            "HandedToCodeThatChangesIt", "LambdaCreatedBeforeTheAsk", "LambdaMadeNotRun",
            "LambdaMadeAfterTheAskAndRun", "LeftBeforeTheAsk", "LeftOpenFor", "MadeInALambda",
            "MeasuredThenRead",
            "MutatedAfterTheLook", "NotCompiledButReportRead", "NotCompiledOffTheList",
            "NotCompiledReadsAllReports", "OptionalIfPresentChanges",
            "ParameterNobodyPasses", "ReadThenChangedThenAsked",
            "ReadThenChangedThenAskedInAMethod", "ReassignedOnOneWay",
            "ReassignedCopyChangedDirectly", "ReassignedCopyHandedToAConsumer",
            "ReplacedAfterTheLook", "ReportsOfAStoreHandedIn", "ReportsOfAnAnsweredModel",
            "ReportsReadOfAModelNobodyAsked",
            "StaticMethodRefReads", "StoreAskOfAnAnswered", "StreamForEachChanges",
            "StructuralFailureOfAnUnasked", "StructuralReportsOfAnUnasked", "SwallowedFailure",
            "ThrownOnTheReadAndCaughtByTheCaller", "TwoBoxesOneFieldName", "UnboundMethodRefReads",
            "UpdatedAfterTheLook",
            "WarningsOfAnUnaskedModel"));

    private static final Set<String> ACCEPTED_SHAPES = new TreeSet<>(List.of(
            "ADerivedModelAsked", "AliasOfAnAskedModel", "AnotherClassAskedAboutIt",
            "AskedAfterTheRead", "AskedByAMethodOfItsOwn", "AskedOnEveryWay", "AskedThenCaptured",
            "AskedThenRead", "ChangesAStoreItWasHandedThatIsNoModels",
            "ConfiguredThroughTheDbBeforeTheLook", "DbHandedToAReader",
            "ErrorsOfAnAnsweredModel", "FieldAskedWhereWritten", "HandedToAnInterfaceThatOnlyLooks",
            "HelperThatChangesAndAsks", "MarkedAndNotRun",
            "NotCompiledOnTheList",
            "ParameterHandedByACaller", "ReportsOfAStoreHandedInAfterTheLook",
            "RequireNonNullKeepsTheAsk", "TheErrorsAreWhatWasMeant",
            "ThroughTheDoor",
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
                () -> "a method reads the report of a model that was not handed to ACompiledModel"
                        + " before the read on every way to it, or after it on every way out, or of"
                        + " a model that cannot be followed to where it was made, or that nothing"
                        + " hands it, or says it did not compile it and is not on the list that may,"
                        + " so the empty report of a model that did not compile passes it; why: "
                        + findings().why());
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
                        "(Ljava/lang/String;)Z")));        List<ClassModel> shapes = new ArrayList<>();
        for (String shape : REFUSED_SHAPES) {
            shapes.add(COMPILED.read(FIXTURES + shape));
        }
        for (String shape : ACCEPTED_SHAPES) {
            shapes.add(COMPILED.read(FIXTURES + shape));
        }
        shapes.add(COMPILED.read(FIXTURES + "Factory"));
        Set<String> refused = new TreeSet<>();
        List<ClassModel> production = new ArrayList<>();
        production.addAll(COMPILED.inTheClassesOf("souther/architecture/fixture"));
        for (Path module : COMPILED.modules()) {
            production.addAll(COMPILED.classesOf(module));
        }
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
     * And what the store can do is each said to read a report, to change what a model is made of,
     * or to do neither.
     *
     * <p>What a method of {@code Compilation} does is worked out from what it can reach of these,
     * so a method added to the store is one the check does not know about until it is said.
     */
    @Test
    void everyMethodOfAModelsStoreIsSaidToReadChangeOrNeither() {
        assertEquals(Set.of(), ModelVocabulary.unsaid(COMPILED.read(ModelVocabulary.DB)),
                "a method of Db is not said in ModelVocabulary to read a report, to change what a"
                        + " model is made of, or to do neither");
    }

    /**
     * And what the working out takes of the shape of a method is held where it is taken.
     *
     * <p>A static method of the model's class is taken to work on the model it makes, so that it
     * changes none that exists; and a method of the store that hands back reports is taken to be
     * the reading of them or the question that holds them. A method added that is neither is one
     * the working out would take wrong.
     */
    @Test
    void whatIsTakenOfAMethodByItsShapeHoldsOfEveryMethodThatHasTheShape() {
        assertEquals(Set.of(), ModelVocabulary.unsaidStatics(
                        COMPILED.read(ModelVocabulary.COMPILATION)),
                "a static method of Compilation takes a model or a store and is not said to read");
        Set<String> reading = new TreeSet<>(ModelVocabulary.DB_READS_A_REPORT);
        reading.addAll(ModelVocabulary.DB_HOLDS_ANSWERS);
        assertEquals(reading,
                ModelVocabulary.handingBackReports(COMPILED.read(ModelVocabulary.DB)),
                "a method of Db hands back reports and is neither the reading of them nor the"
                        + " question that holds them");
    }

    /**
     * And what is worked out of the methods of a model is what they are: every one that reads a
     * report says so, and every one that changes the model does.
     *
     * <p>The methods are worked out from the classes, so this holds the working out to what a
     * reader of the compiler knows of them, and does not list the methods the check follows.
     */
    @Test
    void theMethodsOfAModelThatReadAReportOrChangeItAreFoundFromTheClasses() {
        List<ClassModel> everything = new ArrayList<>();
        for (Path module : COMPILED.modules()) {
            everything.addAll(COMPILED.classesOf(module));
        }
        ModelEffects effects = ModelEffects.of(everything);
        String model = ModelVocabulary.COMPILATION;
        Set<String> reading = new TreeSet<>();
        Set<String> changing = new TreeSet<>();
        for (java.lang.classfile.MethodModel method : COMPILED.read(model).methods()) {
            String key = AMethod.of(model, method.methodName().stringValue(),
                    method.methodType().stringValue());
            if (effects.readsReports(key)) {
                reading.add(method.methodName().stringValue());
            }
            if (effects.changes(key)) {
                changing.add(method.methodName().stringValue());
            }
        }
        assertTrue(reading.containsAll(ModelVocabulary.SHOWS_ERRORS),
                () -> "what shows the errors is said in ModelVocabulary and is a method that reads"
                        + " what a model found: " + reading);
        assertTrue(reading.containsAll(Set.of("reports", "warnings", "adequacy", "diagnostics",
                        "repairs")),
                () -> "what reads the whole of what a model found is found from the classes: "
                        + reading);
        assertTrue(changing.containsAll(Set.of("update", "measure")),
                () -> "changing a model: " + changing);
        Set<String> answersAndChanges = new TreeSet<>(changing);
        answersAndChanges.retainAll(ModelVocabulary.ANSWERS);
        assertEquals(Set.of(), answersAndChanges,
                () -> "answering a model changes what it is made of: " + changing);
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
