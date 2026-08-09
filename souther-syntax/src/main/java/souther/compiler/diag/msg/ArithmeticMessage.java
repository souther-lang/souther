package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What arithmetic refuses, as the rule that refused it. */
public sealed interface ArithmeticMessage extends Message {

    @Code(DiagnosticCode.E1324)
    record AnOperandIsNotANumber(String operand) implements ArithmeticMessage, Reported {}

    @Code(DiagnosticCode.E1324)
    record ANewtypeWithNoDirectNumericBase(String newtype, String wrapped)
            implements ArithmeticMessage, Reported {}

    @Code(DiagnosticCode.E1324)
    record ReachTheBaseWithValue(String newtype, String wrapped) implements ArithmeticMessage, Reported {}

    @Code(DiagnosticCode.E1324)
    record TwoDifferentNewtypes(String left, String right) implements ArithmeticMessage, Reported {}

    @Code(DiagnosticCode.E1324)
    record ConvertOneToTheOthersNewtype() implements ArithmeticMessage, Reported {}

    @Code(DiagnosticCode.E1324)
    record AProductChangesDimension(String left, String right) implements ArithmeticMessage, Reported {}

    @Code(DiagnosticCode.E1324)
    record ComputeOnValueAndBuildTheProduct() implements ArithmeticMessage, Reported {}

    @Code(DiagnosticCode.E1324)
    record AQuotientChangesDimension(String left, String right) implements ArithmeticMessage, Reported {}

    @Code(DiagnosticCode.E1324)
    record ComputeOnValueAndBuildTheQuotient() implements ArithmeticMessage, Reported {}

    @Code(DiagnosticCode.E1324)
    record AValueOfAnotherBase(String newtype, String base, String value)
            implements ArithmeticMessage, Reported {}

    @Code(DiagnosticCode.E1324)
    record WhatEachOperatorTakesBesideANewtype(String newtype, String base)
            implements ArithmeticMessage, Reported {}

    @Code(DiagnosticCode.E1324)
    record OnlyALiteralIsReadAsTheNewtype(String newtype, String value)
            implements ArithmeticMessage, Reported {}

    @Code(DiagnosticCode.E1324)
    record BuildItWhereTheValueComesFrom(String newtype) implements ArithmeticMessage, Reported {}

    @Code(DiagnosticCode.E1324)
    record AReciprocalChangesDimension(String value, String newtype) implements ArithmeticMessage, Reported {}

    @Code(DiagnosticCode.E1324)
    record ComputeOnValueAndBuildTheReciprocal() implements ArithmeticMessage, Reported {}
}
