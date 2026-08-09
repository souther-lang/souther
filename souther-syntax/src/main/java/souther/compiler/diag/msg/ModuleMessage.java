package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What a module, its imports, and what it exposes are told. */
public sealed interface ModuleMessage extends Message {

    @Code(DiagnosticCode.E1321)
    record CannotReadAFieldOnASum(String field, String sum) implements ModuleMessage {}

    @Code(DiagnosticCode.E1321)
    record TheseCasesHaveNoSuchField(String field, String cases) implements ModuleMessage {}

    @Code(DiagnosticCode.E1321)
    record EveryCaseDeclaresItsOwn(String field) implements ModuleMessage {}

    @Code(DiagnosticCode.E2105)
    record TwoMembersJoinThroughOneCaseClass(String one, String other, String caseClass) implements ModuleMessage {}

    @Code(DiagnosticCode.E2105)
    record AMemberGoesByItsOwnNameWithCaseAfterIt() implements ModuleMessage {}

    @Code(DiagnosticCode.E2105)
    record AMemberReachesTheUnionThroughABehavior(String behavior, String member, String through, String caseClass) implements ModuleMessage {}

    @Code(DiagnosticCode.E2105)
    record AMemberReachesTheUnionThroughAData(String data, String member, String through, String caseClass) implements ModuleMessage {}

    @Code(DiagnosticCode.E2105)
    record RenameTheMemberOrTheTypeItCollidesWith(String member) implements ModuleMessage {}

    @Code(DiagnosticCode.E1610)
    record ExposingIsTypeGranular(String write, String notThis) implements ModuleMessage {}

    @Code(DiagnosticCode.E1609)
    record ExposingNamesAnImportedName(String name) implements ModuleMessage {}

    @Code(DiagnosticCode.E1609)
    record ExposingNamesSomethingThisModuleDoesNotDeclare(String name) implements ModuleMessage {}

    @Code(DiagnosticCode.E1508)
    record TheAliasIsAlreadyTaken(String alias, String by) implements ModuleMessage {}

    @Code(DiagnosticCode.E1508)
    record AnAliasIsANameNothingElseAnswersTo() implements ModuleMessage {}

    @Code(DiagnosticCode.E1508)
    record ABehaviorIsNamedFromTwoModules(String behavior, String one, String other) implements ModuleMessage {}

    @Code(DiagnosticCode.E1508)
    record ABehaviorsNameIsAlsoItsInjectedField(String behavior) implements ModuleMessage {}

    @Code(DiagnosticCode.E1508)
    record TheNameIsImportedFromTwoModules(String name, String one, String other) implements ModuleMessage {}

    @Code(DiagnosticCode.E1508)
    record ItWasAlreadyImportedHere(String name, String from) implements ModuleMessage {}

    @Code(DiagnosticCode.E1508)
    record ImportAtMostOneAndQualifyTheOther(String name, String module) implements ModuleMessage {}

    @Code(DiagnosticCode.E1508)
    record TheSameNameIsImportedTwiceFromOneModule() implements ModuleMessage {}

    @Code(DiagnosticCode.E1506)
    record TheModuleDeclaresNoSuchName(String name, String module) implements ModuleMessage {}

    @Code(DiagnosticCode.E1507)
    record TheModuleDoesNotExposeIt(String name, String module) implements ModuleMessage {}

    @Code(DiagnosticCode.E1504)
    record UnknownModule(String module) implements ModuleMessage {}

    @Code(DiagnosticCode.E1922)
    record ImportedButNeverUsedUnderThisName(String name) implements ModuleMessage {}

    @Code(DiagnosticCode.E1922)
    record TakeItOffTheImportList() implements ModuleMessage {}

    @Code(DiagnosticCode.E1503)
    record DuplicateModule(String module) implements ModuleMessage {}

    @Code(DiagnosticCode.E1505)
    record TheModuleWasCompiledByAnotherSouther(String module, String by) implements ModuleMessage {}

    @Code(DiagnosticCode.E1505)
    record RebuildItOrCompileAgainstWhatBuiltIt(String module) implements ModuleMessage {}

    @Code(DiagnosticCode.E1504)
    record AModuleItNeedsIsNotOnThePath(String needed, String module) implements ModuleMessage {}

    @Code(DiagnosticCode.E1504)
    record AddItToThisProjectsDependencies(String module) implements ModuleMessage {}

    @Code(DiagnosticCode.E1504)
    record TheClassCarryingTheDeclarationIsNotOnThePath(String name, String module) implements ModuleMessage {}

    @Code(DiagnosticCode.E1504)
    record TheJarItCameFromIsIncomplete(String jar) implements ModuleMessage {}

    @Code(DiagnosticCode.E1502)
    record TheModuleTakesTheStandardLibraryQualifier(String module) implements ModuleMessage {}

    @Code(DiagnosticCode.E1502)
    record TheModuleIsInTheReservedNamespace(String module) implements ModuleMessage {}

    @Code(DiagnosticCode.E1503)
    record TheModuleIsCompiledHereAndOnThePath(String module) implements ModuleMessage {}

    @Code(DiagnosticCode.E1503)
    record RenameItOrDropTheDependency(String module) implements ModuleMessage {}

    @Code(DiagnosticCode.E1504)
    record TheModuleDeclaresNoSuchQualifiedName(String name, String module) implements ModuleMessage {}

    @Code(DiagnosticCode.E1504)
    record ItIsDeclaredThereAndNotExposed(String name, String module) implements ModuleMessage {}

    @Code(DiagnosticCode.E1504)
    record NoModuleOfThatName(String module, String name) implements ModuleMessage {}

    @Code(DiagnosticCode.E1611)
    record AnExposedFieldRestsOnWhatIsKept(String exposed, String field, String type) implements ModuleMessage {}

    @Code(DiagnosticCode.E1611)
    record AnExposedInputRestsOnWhatIsKept(String exposed, String input) implements ModuleMessage {}

    @Code(DiagnosticCode.E1611)
    record AnExposedOutputRestsOnWhatIsKept(String exposed, String output) implements ModuleMessage {}

    @Code(DiagnosticCode.E1611)
    record AnExposedArgumentRestsOnWhatIsKept(String exposed, String argument, String type) implements ModuleMessage {}

    @Code(DiagnosticCode.E1611)
    record AnExposedValueRestsOnWhatIsKept(String exposed, String stands) implements ModuleMessage {}

    @Code(DiagnosticCode.E1611)
    record WhatReachesOutMayNotRestOnWhatIsKept(String kept, String exposed) implements ModuleMessage {}
}
