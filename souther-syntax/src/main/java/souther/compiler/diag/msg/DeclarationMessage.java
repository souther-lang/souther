package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What a declaration, a composition and the JVM's own limits say. */
public sealed interface DeclarationMessage extends Message {

    @Code(DiagnosticCode.E1321)
    record CannotReadAFieldOnThisValue(String field) implements DeclarationMessage, Reported {}

    @Code(DiagnosticCode.E1802)
    record AppliedToAnotherNumberOfArguments(String what, String takes, String got) implements DeclarationMessage, Reported {}

    @Code(DiagnosticCode.E1317)
    record ItExpectsAnotherType(String what, Object expects, String got) implements DeclarationMessage, Reported {}

    @Code(DiagnosticCode.E1612)
    record AnInjectionTargetCannotDependOnAnything(String behavior) implements DeclarationMessage, Reported {}

    @Code(DiagnosticCode.E1024)
    record ItCannotBeHeldAsAValueHere(String name, String what) implements DeclarationMessage, Reported {}

    @Code(DiagnosticCode.E1817)
    record ItNeedsANumericElement(String call, souther.compiler.diag.Localizable needs, String element) implements DeclarationMessage, Reported {}

    record ThisOperandIs(String type) implements DeclarationMessage, Supporting {}

    @Code(DiagnosticCode.E1816)
    record ItNeedsAnOrderedElement(String call, souther.compiler.diag.Localizable needs, String element) implements DeclarationMessage, Reported {}

    @Code(DiagnosticCode.E1002)
    record ItConstructsWithoutDeclaringIt(String behavior, String data) implements DeclarationMessage, Reported {}

    record AddTheConstructsEntry(String behavior, String data) implements DeclarationMessage, Supporting {}

    @Code(DiagnosticCode.E1006)
    record ItDeclaresConstructsAndNeverBuilds(String behavior, String data) implements DeclarationMessage, Reported {}

    record RemoveTheConstructsEntry(String data) implements DeclarationMessage, Supporting {}

    @Code(DiagnosticCode.E1101)
    record AnInvariantExpressionIsBool(String given) implements DeclarationMessage, Reported {}

    @Code(DiagnosticCode.E1201)
    record TheMatchDoesNotCoverEveryCase(String subject) implements DeclarationMessage, Reported {}

    record AddACaseFor(String cases) implements DeclarationMessage, Supporting {}

    @Code(DiagnosticCode.E1301)
    record NullIsNotPartOfTheLanguage() implements DeclarationMessage, Reported {}

    @Code(DiagnosticCode.E1303)
    record NothingHereIsAskingForNone() implements DeclarationMessage, Reported {}

    record MakeAbsenceACaseOfItsOwnSum() implements DeclarationMessage, Supporting {}

    @Code(DiagnosticCode.E1303)
    record SomeIsNotACall() implements DeclarationMessage, Reported {}

    record WriteTheValueOnItsOwn() implements DeclarationMessage, Supporting {}

    @Code(DiagnosticCode.E1305)
    record AnInjectedBehaviorConstructsWhatIsKept(String behavior, String data) implements DeclarationMessage, Reported {}

    record ExposeItOrMakeItAUnitData(String data) implements DeclarationMessage, Supporting {}

    @Code(DiagnosticCode.E1401)
    record NotABehaviorOrABuiltin(String name) implements DeclarationMessage, Reported {}

    record ImplementItFromJavaInstead() implements DeclarationMessage, Supporting {}

    @Code(DiagnosticCode.E1501)
    record CyclicModuleDependency() implements DeclarationMessage, Reported {}

    @Code(DiagnosticCode.E1602)
    record ItCallsSomethingWithNoImplementation(String let, String called, String behavior) implements DeclarationMessage, Reported {}

    record AddTheDependsOnEntry(String called, String behavior) implements DeclarationMessage, Supporting {}

    @Code(DiagnosticCode.E1603)
    record ItDeclaresDependsOnAndNeverCallsIt(String behavior, String dependency, String let) implements DeclarationMessage, Reported {}

    record RemoveTheDependsOnEntry(String dependency) implements DeclarationMessage, Supporting {}

    @Code(DiagnosticCode.E1604)
    record TheDeclaredOutputIsNotWhatThePipelineProduces(String behavior, String declared, String produces) implements DeclarationMessage, Reported {}

    record UpdateTheOutputOrHandleTheCase() implements DeclarationMessage, Supporting {}

    @Code(DiagnosticCode.E1605)
    record AnExposedCompositionDeclaresItsOutput(String composition) implements DeclarationMessage, Reported {}

    record WriteTheOutputSignature(String composition, String output) implements DeclarationMessage, Supporting {}

    @Code(DiagnosticCode.E1605)
    record OnlyACompositionTakesAnOutputSignature(String name) implements DeclarationMessage, Reported {}

    @Code(DiagnosticCode.E1607)
    record DependsOnNamesNoSuchBehavior(String behavior, String dependency) implements DeclarationMessage, Reported {}

    record DeclareItHereOrImportIt(String dependency) implements DeclarationMessage, Supporting {}

    @Code(DiagnosticCode.E1607)
    record DependsOnNamesAComposition(String behavior, String dependency) implements DeclarationMessage, Reported {}

    @Code(DiagnosticCode.E1607)
    record DependsOnNamesSomethingThatDependsOnNothing(String behavior, String dependency) implements DeclarationMessage, Reported {}

    @Code(DiagnosticCode.E1608)
    record ABehaviorReachesItself(String behavior, String through) implements DeclarationMessage, Reported {}

    record ABehaviorDoesNotRecurse() implements DeclarationMessage, Supporting {}

    @Code(DiagnosticCode.E1701)
    record TheseBehaviorsCannotBeComposed() implements DeclarationMessage, Reported {}

    record MakeTheLeftOutputACaseTheRightAccepts() implements DeclarationMessage, Supporting {}

    @Code(DiagnosticCode.E2101)
    record ADataNeedsMoreSlotsThanAConstructorHolds(String data, String needs, String holds) implements DeclarationMessage, Reported {}

    @Code(DiagnosticCode.E2101)
    record AHelperTakesMoreParametersThanAMethodHolds(String helper, String takes, String holds) implements DeclarationMessage, Reported {}

    @Code(DiagnosticCode.E2101)
    record ABehaviorTakesMoreParametersThanApplyHolds(String behavior, String takes, String holds) implements DeclarationMessage, Reported {}

    @Code(DiagnosticCode.E2101)
    record ABehaviorHasMoreDependenciesThanAConstructorHolds(String behavior, String has, String holds) implements DeclarationMessage, Reported {}

    @Code(DiagnosticCode.E2102)
    record AMethodIsLargerThanTheJvmHolds(String owner, String method, String bytes, String holds) implements DeclarationMessage, Reported {}

    record SplitTheWorkOrMoveTheTable() implements DeclarationMessage, Supporting {}

    @Code(DiagnosticCode.E2103)
    record AClassNeedsMoreConstantsThanItHolds(String owner, String needs, String holds) implements DeclarationMessage, Reported {}

    @Code(DiagnosticCode.E2103)
    record AClassRefersPastTheConstantPool(String owner, String refersTo, String holds) implements DeclarationMessage, Reported {}

    record MoveTheTableOutOfTheSource() implements DeclarationMessage, Supporting {}

    record RemoveItAndCallItDirectly(String dependency) implements DeclarationMessage, Supporting {}

    record ACompositionsRequirementsAreNotWritten(String dependency)
            implements DeclarationMessage, Supporting {}

    @Code(DiagnosticCode.E2104)
    record ItNestsDeeperThanIsRead() implements DeclarationMessage, Reported {}

    @Code(DiagnosticCode.E2107)
    record ABlockHasMoreStatementsThanADefinitionHolds(int statements, int holds)
            implements DeclarationMessage, Reported {}

    @Code(DiagnosticCode.E2107)
    record ADefinitionIsMoreStructureThanIsHeld(String definition, int costs, int holds)
            implements DeclarationMessage, Reported {}

    @Code(DiagnosticCode.E2107)
    record SubstitutingAValueIsMoreStructureThanIsHeld(String value, int costs, int holds)
            implements DeclarationMessage, Reported {}

    record WriteItAsABehaviorOfItsOwn() implements DeclarationMessage, Supporting {}

    @Code(DiagnosticCode.E2302)
    record TheRightSideOfAValuePipeIsACall() implements DeclarationMessage, Reported {}

    record SplitTheDataAndHoldThemAsFields(String data) implements DeclarationMessage, Supporting {}

    record GroupTheParametersIntoAData() implements DeclarationMessage, Supporting {}

    record GroupTheDependenciesBehindABehavior() implements DeclarationMessage, Supporting {}
}
