package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What a helper, a function passed to one, and a `let` implementing a behavior are told. */
public sealed interface HelperMessage extends Message {

    // --- a helper's own declaration ---

    /** A helper's parameter is written without the type it takes. */
    @Code(DiagnosticCode.E1811)
    record AParameterNeedsItsType(String helper, String parameter) implements HelperMessage, Reported {}

    /** The body does not determine the parameter's type. */
    @Code(DiagnosticCode.E1811)
    record AParameterIsNotDeterminedByTheBody(String helper, String parameter)
            implements HelperMessage, Reported {}

    /** Where the use that fails to determine it is pointed at. */
    record ThisUseNamesNoType() implements HelperMessage, Supporting {}

    /** The parameter is only ever read through a field, which names no type. */
    @Code(DiagnosticCode.E1811)
    record AParameterIsOnlyReadThroughAField(String helper, String parameter)
            implements HelperMessage, Reported {}

    /** Where the field read that fails to determine it is pointed at. */
    record AFieldIsReadOffItAndThatNamesNoType() implements HelperMessage, Supporting {}

    /** A parameter used as a function must be written with its type. */
    @Code(DiagnosticCode.E1811)
    record AFunctionTypedParameterNeedsItsType(String helper, String parameter)
            implements HelperMessage, Reported {}

    /** The body answers something other than what the helper declares. */
    @Code(DiagnosticCode.E1812)
    record TheBodyIsNotWhatTheHelperDeclares(String helper, String declared, String body)
            implements HelperMessage, Reported {}

    /** A helper is called with a number of arguments it does not take. */
    @Code(DiagnosticCode.E1802)
    record CalledWithAnotherNumberOfArguments(String helper, String takes, String called)
            implements HelperMessage, Reported {}

    // --- what is passed to one ---

    /** A block passed to a function parameter takes a different number of arguments. */
    @Code(DiagnosticCode.E1802)
    record TheBlockTakesAnotherNumberOfArguments(String parameter, String helper, String takes,
                                                 String written) implements HelperMessage, Reported {}

    /** A block passed to a function parameter answers the wrong type. */
    @Code(DiagnosticCode.E1805)
    record TheBlockAnswersAnotherType(String parameter, String helper, String must, String returns)
            implements HelperMessage, Reported {}

    /** A value is passed where a function is taken. */
    @Code(DiagnosticCode.E1803)
    record AValueWhereAFunctionIsTaken(String parameter, String helper, String written)
            implements HelperMessage, Reported {}

    /** A lambda is written on an argument that takes a value, and another takes the function. */
    @Code(DiagnosticCode.E1804)
    record TheFunctionGoesToAnotherArgument(String call, String at, String parameter,
                                            String functionAt, String functionParameter)
            implements HelperMessage, Reported {}

    /** What that call reads as, written out. */
    record WriteTheCallThisWay(String call, String shape) implements HelperMessage, Supporting {}

    /** A value is written on the argument that takes the function. */
    @Code(DiagnosticCode.E1804)
    record ThisArgumentTakesAFunction(String call, String at, String parameter)
            implements HelperMessage, Reported {}

    /** A lambda or a field getter is written on an argument that takes neither. */
    @Code(DiagnosticCode.E1804)
    record ThisArgumentTakesNoFunction(String call, String at, String parameter)
            implements HelperMessage, Reported {}

    /** An operation is written without the block it takes. */
    @Code(DiagnosticCode.E1804)
    record ThisExpectsABlock(String call) implements HelperMessage, Reported {}

    /** A function is called with a number of arguments it does not take. */
    @Code(DiagnosticCode.E1802)
    record TheFunctionTakesAnotherNumberOfArguments(String call, String called, String takes)
            implements HelperMessage, Reported {}

    /** A block is written with a number of parameters the position does not take. */
    @Code(DiagnosticCode.E1802)
    record TheBlockIsWrittenWithAnotherNumberOfParameters(String takes, String written)
            implements HelperMessage, Reported {}

    /** A lambda is applied with a number of arguments it does not take. */
    @Code(DiagnosticCode.E1802)
    record TheLambdaIsAppliedWithAnotherNumberOfArguments(String takes, String applied)
            implements HelperMessage, Reported {}

    /** What the function is given is not what it takes. */
    @Code(DiagnosticCode.E1806)
    record TheFunctionTakesAnotherType(String call, String given, String takes)
            implements HelperMessage, Reported {}

    /** A fold's step answers a type the accumulator it builds cannot hold. */
    @Code(DiagnosticCode.E1806)
    record TheStepAnswersAnotherTypeThanTheAccumulator(String call, String answers,
            String accumulator) implements HelperMessage, Reported {}

    /** A function value's type cannot be read where it is written. */
    @Code(DiagnosticCode.E1808)
    record TheFunctionsTypeCannotBeRead(String name) implements HelperMessage, Reported {}

    /** One function value is applied at two argument types. */
    @Code(DiagnosticCode.E1807)
    record TheFunctionIsAppliedAtTwoTypes(String name, String one, String other)
            implements HelperMessage, Reported {}

    /** Two branches answer function values of different types. */
    @Code(DiagnosticCode.E1807)
    record TheBranchesAnswerDifferentFunctionTypes(String one, String other)
            implements HelperMessage, Reported {}

    /** A binding holding a function carries an annotation that is not a function type. */
    @Code(DiagnosticCode.E1810)
    record AnAnnotationOnAFunctionBindingIsNotAFunctionType(String binding)
            implements HelperMessage, Reported {}

    /** What to do about it. */
    record WriteAFunctionTypeOrLeaveTheAnnotationOff() implements HelperMessage, Supporting {}
}
