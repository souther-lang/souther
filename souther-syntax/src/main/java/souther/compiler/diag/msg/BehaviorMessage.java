package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What a behavior, the `let` that implements it, and a composition of them are told. */
public sealed interface BehaviorMessage extends Message {

    @Code(DiagnosticCode.E2105)
    record TwoBehaviorsCapitalizeToOneClass(String one, String other, String jvmClass) implements BehaviorMessage, Reported {}

    @Code(DiagnosticCode.E2105)
    record ABehaviorCapitalizesOntoAData(String behavior, String jvmClass) implements BehaviorMessage, Reported {}

    @Code(DiagnosticCode.E1818)
    record ABehaviorCannotBeCalledFromHere(String behavior) implements BehaviorMessage, Reported {}

    record WhatReachesABehavior(String behavior) implements BehaviorMessage, Supporting {}

    @Code(DiagnosticCode.E1317)
    record TheBodyIsNotWhatTheBehaviorReturns(String behavior, String returns, String body) implements BehaviorMessage, Reported {}

    @Code(DiagnosticCode.E1615)
    record TheImplementationTakesAnotherNumberOfParameters(String let, String takes, String behavior, String inputs, String injected) implements BehaviorMessage, Reported {}

    @Code(DiagnosticCode.E1614)
    record ACompositionIsAlreadyItsOwnImplementation(String name) implements BehaviorMessage, Reported {}

    @Code(DiagnosticCode.E1615)
    record AnImplementationsParametersTakeTheirTypesFromIt(String let, String behavior, String parameter) implements BehaviorMessage, Reported {}

    @Code(DiagnosticCode.E1615)
    record AnImplementationsReturnComesFromTheBehavior(String let, String behavior) implements BehaviorMessage, Reported {}

    @Code(DiagnosticCode.E1615)
    record AnInjectedParameterIsOutOfOrder(String let, String parameter, String shouldBe) implements BehaviorMessage, Reported {}

    @Code(DiagnosticCode.E1703)
    record ABoundaryEdgeIsNotAStage() implements BehaviorMessage, Reported {}

    @Code(DiagnosticCode.E1702)
    record AStageAfterTheFirstTakesOneInput(String stage, String takes, String pipeline) implements BehaviorMessage, Reported {}

    @Code(DiagnosticCode.E1608)
    record APipelineComposesWithItself(String pipeline) implements BehaviorMessage, Reported {}

    @Code(DiagnosticCode.E2105)
    record AUnionOutputsInterfaceCollidesWithABehavior(String behavior, String jvmClass, String other) implements BehaviorMessage, Reported {}

    @Code(DiagnosticCode.E2105)
    record AUnionOutputsInterfaceCollidesWithAData(String behavior, String jvmClass) implements BehaviorMessage, Reported {}

    record AUnionOutputReachesJavaThroughThatName(String jvmClass) implements BehaviorMessage, Supporting {}

    @Code(DiagnosticCode.E1021)
    record ASumContainsItself(String sum, String through) implements BehaviorMessage, Reported {}

    @Code(DiagnosticCode.E1606)
    record ACaseIsDeclaredInAnotherModule(String caseName, String sum, String module) implements BehaviorMessage, Reported {}

    record ASumsCasesAreDeclaredWithIt(String caseName) implements BehaviorMessage, Supporting {}

    @Code(DiagnosticCode.E1502)
    record ABuiltInOptionCaseCannotBeDeclared(String name) implements BehaviorMessage, Reported {}

    @Code(DiagnosticCode.E1020)
    record UnknownCaseInASum(String caseName, String sum) implements BehaviorMessage, Reported {}

    @Code(DiagnosticCode.E2001)
    record NotStructurallyRecursive(String helper) implements BehaviorMessage, Reported {}

    @Code(DiagnosticCode.E2001)
    record APartialHelperIsWrittenWhereAValueGoes(String helper) implements BehaviorMessage, Reported {}

    @Code(DiagnosticCode.E2001)
    record ItReachesAPartialHelper(String helper, String partial, String through) implements BehaviorMessage, Reported {}

    @Code(DiagnosticCode.E2001)
    record NotSizeChangeTerminating(String helpers) implements BehaviorMessage, Reported {}

    @Code(DiagnosticCode.E2001)
    record TooComplexToProveTotal(String helpers) implements BehaviorMessage, Reported {}
}
