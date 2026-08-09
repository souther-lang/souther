package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What arithmetic refuses, as the rule that refused it. */
public sealed interface ArithmeticMessage extends Message {

    @Code(DiagnosticCode.E1324)
    record AnOperandIsNotANumber(String operand) implements ArithmeticMessage, Reported {}

    @Code(DiagnosticCode.E1324)
    record ANewtypeWithNoDirectNumericBase(String newtype, String wrapped)
            implements ArithmeticMessage, Reported {}

    record ReachTheBaseWithValue(String newtype, String wrapped) implements ArithmeticMessage, Supporting {}

    @Code(DiagnosticCode.E1324)
    record TwoDifferentNewtypes(String left, String right) implements ArithmeticMessage, Reported {}

    record ConvertOneToTheOthersNewtype() implements ArithmeticMessage, Supporting {}

    @Code(DiagnosticCode.E1324)
    record AProductChangesDimension(String left, String right) implements ArithmeticMessage, Reported {}

    record ComputeOnValueAndBuildTheProduct() implements ArithmeticMessage, Supporting {}

    @Code(DiagnosticCode.E1324)
    record AQuotientChangesDimension(String left, String right) implements ArithmeticMessage, Reported {}

    record ComputeOnValueAndBuildTheQuotient() implements ArithmeticMessage, Supporting {}

    @Code(DiagnosticCode.E1324)
    record AValueOfAnotherBase(String newtype, String base, String value)
            implements ArithmeticMessage, Reported {}

    record WhatEachOperatorTakesBesideANewtype(String newtype, String base)
            implements ArithmeticMessage, Supporting {}

    @Code(DiagnosticCode.E1324)
    record OnlyALiteralIsReadAsTheNewtype(String newtype, String value)
            implements ArithmeticMessage, Reported {}

    record BuildItWhereTheValueComesFrom(String newtype) implements ArithmeticMessage, Supporting {}

    @Code(DiagnosticCode.E1324)
    record AReciprocalChangesDimension(String value, String newtype) implements ArithmeticMessage, Reported {}

    record ComputeOnValueAndBuildTheReciprocal() implements ArithmeticMessage, Supporting {}
}
