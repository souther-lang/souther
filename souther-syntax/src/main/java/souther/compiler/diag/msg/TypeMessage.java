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

    /** An `else` arm the branches were not joinable at, against the join of the branches before it.
     * An `else` answering per clause folds its arms, so the second type is an accumulator. */
    @Code(DiagnosticCode.E1208)
    record ThisBranchAndThePrecedingOnes(String branch, String preceding)
            implements TypeMessage, Reported {}

    record TheThenBranchProduces(String type) implements TypeMessage, Supporting {}

    record TheElseBranchProduces(String type) implements TypeMessage, Supporting {}

    record MakeBothBranchesProduceOneType() implements TypeMessage, Supporting {}

    /** An element a list's elements were not joinable at, against the join of the ones before it.
     * The second type is an accumulator and no element's own, so it is said rather than pointed at. */
    @Code(DiagnosticCode.E1318)
    record ThisElementAndThePrecedingOnes(String element, String preceding)
            implements TypeMessage, Reported {}

    /** Two lists `++` joins whose element types do not. Both are operands, so both carry a region
     * and the message names neither. */
    @Code(DiagnosticCode.E1318)
    record TheTwoListsHoldDifferentElements() implements TypeMessage, Reported {}

    record ThisListHoldsElementsOf(String element) implements TypeMessage, Supporting {}

    record MakeEveryElementTheSameType() implements TypeMessage, Supporting {}

    @Code(DiagnosticCode.E1314)
    record AFieldsMapCannotBeKeyedByThat(String field, String key) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1314)
    record AnOutputMapCannotBeKeyedByThat(String behavior, String key) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1314)
    record AParameterMapCannotBeKeyedByThat(String parameter, String key) implements TypeMessage, Reported {}

    record AMapIsAJsonObjectKeyedByStrings() implements TypeMessage, Supporting {}

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

    record AnnotateThePositionTheCallFeeds() implements TypeMessage, Supporting {}

    record MapToTheNumericFieldFirst(String call) implements TypeMessage, Supporting {}

    @Code(DiagnosticCode.E1317)
    record ItAnswersANumberAndThisPositionNeedsAnother(String call, String needed) implements TypeMessage, Reported {}

    record ANewtypeIsBuiltFromTheResult(String call) implements TypeMessage, Supporting {}

    @Code(DiagnosticCode.E1206)
    record ThePatternOpensAnotherType(String opens, String value) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1206)
    record NotANewtypeToOpenInABinding(String name) implements TypeMessage, Reported {}

    record ABindingOpensOnlyWhatEveryValueHas() implements TypeMessage, Supporting {}

    record AModelTypeOwnsTheAbsence() implements TypeMessage, Supporting {}

    @Code(DiagnosticCode.E1816)
    record TheKeyMustBeAnOrderedValue(String call, String returns) implements TypeMessage, Reported {}

    record MapToAnOrderedFieldFirst() implements TypeMessage, Supporting {}

    @Code(DiagnosticCode.E1325)
    record AParameterTakesATypeTheLanguageDeclares(String parameter, String type) implements TypeMessage, Reported {}

    /** A data field is written from a type the language declares of its own operations. A field
     *  crosses, so it carries the model's own vocabulary as a behavior's boundary does. */
    @Code(DiagnosticCode.E1325)
    record AFieldTakesATypeTheLanguageDeclares(String field, String type) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1311)
    record AParameterCarriesAFunction(String parameter, String type) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1313)
    record AParameterCarriesAnOptional(String parameter, String type) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1311)
    record AParameterIsATuple(String parameter) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1312)
    record AParameterIsAnAnonymousUnion(String parameter, String type) implements TypeMessage, Reported {}

    record DeclareItAsATypeOfTheModel() implements TypeMessage, Supporting {}

    @Code(DiagnosticCode.E1322)
    record ATemporalTakesAWrittenString(String type) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1322)
    record ThatIsNotATemporalOfThatKind(String type, String written) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1322)
    record AnInstantIsWrittenInUtc(String written) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1322)
    record ALeapSecondIsNotAMoment(String written) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1322)
    record ATimeOfDayIsWrittenToTheSecond(String type, String written) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1320)
    record ThePatternBindsAnotherNumberOfNames(String binds, String holds) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1320)
    record ATuplePatternNeedsATuple(String given) implements TypeMessage, Reported {}

    @Code(DiagnosticCode.E1317)
    record ItDoesNotHaveTheTypeItNeedsHere(String what) implements TypeMessage, Reported {}

    record AdjustTheValueOrThePosition() implements TypeMessage, Supporting {}

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

    record AMemberIsNamedByItsWrittenName() implements TypeMessage, Supporting {}

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
