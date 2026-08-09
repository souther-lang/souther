package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What a type, an operator and a boundary position are told. */
public sealed interface TypeMessage extends Message {

    @Code(DiagnosticCode.E1319)
    record TheseTwoCannotBeCompared(String one, String other) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1319)
    record ComparisonNeedsOrderedValuesOfOneType(String one, String other) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1319)
    record JoinsTwoListsOrTwoStrings(String one, String other) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1319)
    record AFunctionHasNoValueToCompare(String given) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1319)
    record UnaryMinusNeedsANumber(String given) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1208)
    record TheBranchesOfThisIfDisagree() implements TypeMessage, Reported {}

    record TheThenBranchProduces(String type) implements TypeMessage {}

    record TheElseBranchProduces(String type) implements TypeMessage {}

    record MakeBothBranchesProduceOneType() implements TypeMessage {}

    @Code(DiagnosticCode.E1318)
    record TheElementsDoNotAllHaveOneType() implements TypeMessage, Reported {}

    record OneElementIsOneAndAnotherIsAnother(String one, String other) implements TypeMessage {}

    @Code(DiagnosticCode.E1314)
    record AFieldsMapCannotBeKeyedByThat(String field, String key) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1314)
    record AnOutputMapCannotBeKeyedByThat(String behavior, String key) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1314)
    record AParameterMapCannotBeKeyedByThat(String parameter, String key) implements TypeMessage, Reported {}

    record AMapIsAJsonObjectKeyedByStrings() implements TypeMessage {}

    @Code(DiagnosticCode.E1315)
    record AMapKeyIsComparedAndAFunctionIsNot(String given) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1315)
    record ASetElementIsComparedAndAFunctionIsNot(String given) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1323)
    record ThePatternMustBeWrittenOut() implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1323)
    record ThePatternIsNotARegularExpression(String why) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1815)
    record OverTheEmptyListTheSeedDecides(String call) implements TypeMessage, Reported {}

    record AnnotateThePositionTheCallFeeds() implements TypeMessage {}

    record MapToTheNumericFieldFirst(String call) implements TypeMessage {}

    @Code(DiagnosticCode.E1317)
    record ItAnswersANumberAndThisPositionNeedsAnother(String call, String needed) implements TypeMessage, Reported {}

    record ANewtypeIsBuiltFromTheResult(String call) implements TypeMessage {}

    @Code(DiagnosticCode.E1206)
    record ThePatternOpensAnotherType(String opens, String value) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1206)
    record NotANewtypeToOpenInABinding(String name) implements TypeMessage, Reported {}

    record ABindingOpensOnlyWhatEveryValueHas() implements TypeMessage {}

    record AModelTypeOwnsTheAbsence() implements TypeMessage {}

    @Code(DiagnosticCode.E1816)
    record TheKeyMustBeAnOrderedValue(String call, String returns) implements TypeMessage, Reported {}

    record MapToAnOrderedFieldFirst() implements TypeMessage {}

    @Code(DiagnosticCode.E1325)
    record AParameterTakesATypeTheLanguageDeclares(String parameter, String type) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1311)
    record AParameterCarriesAFunction(String parameter, String type) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1313)
    record AParameterCarriesAnOptional(String parameter, String type) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1311)
    record AParameterIsATuple(String parameter) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1312)
    record AParameterIsAnAnonymousUnion(String parameter, String type) implements TypeMessage, Reported {}

    record DeclareItAsATypeOfTheModel() implements TypeMessage {}

    @Code(DiagnosticCode.E1322)
    record ATemporalTakesAWrittenString(String type) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1322)
    record ThatIsNotATemporalOfThatKind(String type, String written) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1320)
    record ThePatternBindsAnotherNumberOfNames(String binds, String holds) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1320)
    record ATuplePatternNeedsATuple(String given) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1317)
    record ItDoesNotHaveTheTypeItNeedsHere(String what) implements TypeMessage, Reported {}

    record AdjustTheValueOrThePosition() implements TypeMessage {}

    @Code(DiagnosticCode.E1316)
    record AListNeedsItsElementType() implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1316)
    record AMapNeedsItsValueType() implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1316)
    record AnOptionNeedsItsTypeArgument() implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1316)
    record ASetNeedsItsElementType() implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1613)
    record NotAUnionMember(String member) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1613)
    record OneNameForTwoMembers(String name, String one, String other) implements TypeMessage, Reported {}

    record AMemberIsNamedByItsWrittenName() implements TypeMessage {}

    @Code(DiagnosticCode.E1317)
    record ItExpectedOneTypeAndGotAnother(String what, String expected, String got) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1311)
    record AnOutputIsATuple(String behavior) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1311)
    record AnOutputCarriesAFunction(String behavior, String type) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1313)
    record AnOutputCarriesAnOptional(String behavior, String type) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1325)
    record AnOutputIsATypeTheLanguageDeclares(String behavior, String type) implements TypeMessage, Reported {}
}
