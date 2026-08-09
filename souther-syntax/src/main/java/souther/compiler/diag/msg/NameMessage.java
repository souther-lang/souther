package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What a name, a binding and an application are told. */
public sealed interface NameMessage extends Message {

    @Code(DiagnosticCode.E1803)
    record ItIsNotAFunctionHere(String name) implements NameMessage, Reported {}

    @Code(DiagnosticCode.E1809)
    record ABlockIsNotAValue() implements NameMessage, Reported {}

    @Code(DiagnosticCode.E1803)
    record ANameTheLanguageGivesIsNotAFunction(String name) implements NameMessage, Reported {}

    @Code(DiagnosticCode.E1019)
    record ABindingMayNotShadowABuiltIn(String name) implements NameMessage, Reported {}

    @Code(DiagnosticCode.E1815)
    record TheElementTypeCannotBeInferredHere() implements NameMessage, Reported {}

    record TheAccumulatorsTypeStaysUnknown() implements NameMessage, Supporting {}

    @Code(DiagnosticCode.E1317)
    record TheBindingDeclaresAnotherType(String binding, String declares, String value) implements NameMessage, Reported {}

    @Code(DiagnosticCode.E1814)
    record ARecursiveHelperIsPure(String helper, String injected) implements NameMessage, Reported {}

    @Code(DiagnosticCode.E1813)
    record ARecursiveHelperMustDeclareItsReturnType(String helper) implements NameMessage, Reported {}

    @Code(DiagnosticCode.E1506)
    record NotAStandardLibraryFunction(String name) implements NameMessage, Reported {}

    @Code(DiagnosticCode.E1025)
    record WriteAStandardLibraryNameQualified(String name, String qualified) implements NameMessage, Reported {}

    record WriteItOnItsOwn(String name) implements NameMessage, Supporting {}

    @Code(DiagnosticCode.E1023)
    record NoBehaviorOfThatNameInThisPipeline(String name) implements NameMessage, Reported {}

    @Code(DiagnosticCode.E1023)
    record NoValueOfThatNameInScope(String name) implements NameMessage, Reported {}

    @Code(DiagnosticCode.E1023)
    record NoTypeOfThatName(String name) implements NameMessage, Reported {}

    @Code(DiagnosticCode.E1307)
    record NothingSaysWhatThisPositionHolds() implements NameMessage, Reported {}

    record WriteItWhereTheTypeIsStated() implements NameMessage, Supporting {}

    @Code(DiagnosticCode.E1022)
    record AValueReachesItself(String name, String through) implements NameMessage, Reported {}
}
