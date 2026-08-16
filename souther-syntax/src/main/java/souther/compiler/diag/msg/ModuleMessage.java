package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What a module, its imports, and what it exposes are told. */
public sealed interface ModuleMessage extends Message {

    @Code(DiagnosticCode.E1321)
    record CannotReadAFieldOnASum(String field, String sum) implements ModuleMessage, Reported {}

    record TheseCasesHaveNoSuchField(String field, String cases) implements ModuleMessage, Supporting {}

    record EveryCaseDeclaresItsOwn(String field) implements ModuleMessage, Supporting {}

    @Code(DiagnosticCode.E2105)
    record TwoMembersJoinThroughOneCaseClass(String one, String other, String caseClass) implements ModuleMessage, Reported {}

    record AMemberGoesByItsOwnNameWithCaseAfterIt() implements ModuleMessage, Supporting {}

    @Code(DiagnosticCode.E2105)
    record AMemberReachesTheUnionThroughABehavior(String behavior, String member, String through, String caseClass) implements ModuleMessage, Reported {}

    @Code(DiagnosticCode.E2105)
    record AMemberReachesTheUnionThroughAData(String data, String member, String through, String caseClass) implements ModuleMessage, Reported {}

    record RenameTheMemberOrTheTypeItCollidesWith(String member) implements ModuleMessage, Supporting {}

    @Code(DiagnosticCode.E1610)
    record ExposingIsTypeGranular(String write, String notThis) implements ModuleMessage, Reported {}

    @Code(DiagnosticCode.E1609)
    record ExposingNamesAnImportedName(String name) implements ModuleMessage, Reported {}

    @Code(DiagnosticCode.E1609)
    record ExposingNamesSomethingThisModuleDoesNotDeclare(String name) implements ModuleMessage, Reported {}

    @Code(DiagnosticCode.E1508)
    record TheAliasIsAlreadyTaken(String alias, String by) implements ModuleMessage, Reported {}

    record AnAliasIsANameNothingElseAnswersTo() implements ModuleMessage, Supporting {}

    @Code(DiagnosticCode.E1508)
    record ABehaviorIsNamedFromTwoModules(String behavior, String one, String other) implements ModuleMessage, Reported {}

    record ABehaviorsNameIsAlsoItsInjectedField(String behavior) implements ModuleMessage, Supporting {}

    @Code(DiagnosticCode.E1508)
    record TheNameIsImportedFromTwoModules(String name, String one, String other) implements ModuleMessage, Reported {}

    record ItWasAlreadyImportedHere(String name, String from) implements ModuleMessage, Supporting {}

    record ImportAtMostOneAndQualifyTheOther(String name, String module) implements ModuleMessage, Supporting {}

    record TheSameNameIsImportedTwiceFromOneModule() implements ModuleMessage, Supporting {}

    @Code(DiagnosticCode.E1506)
    record TheModuleDeclaresNoSuchName(String name, String module) implements ModuleMessage, Reported {}

    @Code(DiagnosticCode.E1507)
    record TheModuleDoesNotExposeIt(String name, String module) implements ModuleMessage, Reported {}

    @Code(DiagnosticCode.E1504)
    record UnknownModule(String module) implements ModuleMessage, Reported {}

    @Code(DiagnosticCode.E1922)
    record ImportedButNeverUsedUnderThisName(String name) implements ModuleMessage, Reported {}

    record TakeItOffTheImportList() implements ModuleMessage, Supporting {}

    @Code(DiagnosticCode.E1503)
    record DuplicateModule(String module) implements ModuleMessage, Reported {}

    /**
     * A module the class path carries and this compiler will not read.
     *
     * <p>One thing to be told, whatever went wrong inside the artifact. What an importing author can
     * do about it is the same in every case — rebuild the dependency, or compile against what built
     * it — and each of the ways it can fail is a fact about somebody else's build, said as a note
     * under this rather than as a rule of its own that the author never broke.
     *
     * <p>Which is what puts it at the right level. A boundary revision that does not agree, a class
     * the jar left out and a declaration this compiler cannot parse are three different rules about
     * publishing, and an author reading a report about their own import needs none of them named as
     * the rule they are in breach of.
     */
    @Code(DiagnosticCode.E1509)
    record TheModuleCannotBeReadBack(String module) implements ModuleMessage, Reported {}

    /** Why: the artifact records a boundary revision this compiler does not agree with. */
    record ItWasBuiltBy(String by) implements ModuleMessage, Supporting {}

    /** Why: it names a declaration whose class the path does not carry. */
    record AClassItSaysItDeclaresIsNotOnThePath(String declaration) implements ModuleMessage, Supporting {}

    /** Why: one of its classes carries metadata this compiler cannot read. */
    record ItsMetadataCannotBeReadHere() implements ModuleMessage, Supporting {}

    /** Why: what it carries declares a different module from the one it was filed under. */
    record ItDeclaresAnotherModule(String named) implements ModuleMessage, Supporting {}

    /** Why: what it published is not source this compiler parses. Nothing about where — the text was
     *  put back together here, so a line of it is a line of nothing anybody holds. */
    record WhatItPublishedIsNotSourceThisCompilerParses() implements ModuleMessage, Supporting {}

    /** Why: one of its import lines is not one this compiler can read. Which of the ways a line can
     *  fail is the publishing project's to see in its own build; here they come to the same thing. */
    record AnImportLineOfItsCannotBeReadHere(String name, String from) implements ModuleMessage, Supporting {}

    record RebuildItOrCompileAgainstWhatBuiltIt(String module) implements ModuleMessage, Supporting {}

    @Code(DiagnosticCode.E1504)
    record AModuleItNeedsIsNotOnThePath(String needed, String module) implements ModuleMessage, Reported {}

    record AddItToThisProjectsDependencies(String module) implements ModuleMessage, Supporting {}

    /** Another import of this compilation that arrives at the same declaration. A finding and not an
     * explanation: the two imports are not measured against each other, and the author of either
     * file has the same thing to do about it. */
    record ItIsReachedFromHereToo() implements ModuleMessage, FindingRegion {}

    @Code(DiagnosticCode.E1502)
    record TheModuleTakesTheStandardLibraryQualifier(String module) implements ModuleMessage, Reported {}

    @Code(DiagnosticCode.E1502)
    record TheModuleIsInTheReservedNamespace(String module) implements ModuleMessage, Reported {}

    @Code(DiagnosticCode.E1503)
    record TheModuleIsCompiledHereAndOnThePath(String module) implements ModuleMessage, Reported {}

    record RenameItOrDropTheDependency(String module) implements ModuleMessage, Supporting {}

    @Code(DiagnosticCode.E1506)
    record TheModuleDeclaresNoSuchQualifiedName(String name, String module) implements ModuleMessage, Reported {}

    @Code(DiagnosticCode.E1507)
    record ItIsDeclaredThereAndNotExposed(String name, String module) implements ModuleMessage, Reported {}

    @Code(DiagnosticCode.E1504)
    record NoModuleOfThatName(String module, String name) implements ModuleMessage, Reported {}

    @Code(DiagnosticCode.E1611)
    record AnExposedFieldRestsOnWhatIsKept(String exposed, String field, String type) implements ModuleMessage, Reported {}

    @Code(DiagnosticCode.E1611)
    record AnExposedInputRestsOnWhatIsKept(String exposed, String input) implements ModuleMessage, Reported {}

    @Code(DiagnosticCode.E1611)
    record AnExposedOutputRestsOnWhatIsKept(String exposed, String output) implements ModuleMessage, Reported {}

    @Code(DiagnosticCode.E1611)
    record AnExposedArgumentRestsOnWhatIsKept(String exposed, String argument, String type) implements ModuleMessage, Reported {}

    @Code(DiagnosticCode.E1611)
    record AnExposedValueRestsOnWhatIsKept(String exposed, String stands) implements ModuleMessage, Reported {}

    record WhatReachesOutMayNotRestOnWhatIsKept(String kept, String exposed) implements ModuleMessage, Supporting {}
}
