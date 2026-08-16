package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What a `data` declaration and a construction of one are told. */
public sealed interface DataMessage extends Message {

    /** Two spreads, or a spread and the declaration itself, supply one field name. */
    @Code(DiagnosticCode.E1004)
    record SpreadFieldCollision(String field, String from, String heldBy) implements DataMessage, Reported {}

    /** What is spread is not a product data. */
    @Code(DiagnosticCode.E1015)
    record SpreadIsNotAProductData(String spread) implements DataMessage, Reported {}

    /** What is spread in a construction is neither a data value nor a sum whose cases agree. */
    @Code(DiagnosticCode.E1015)
    record SpreadIsNotADataValue(String spread) implements DataMessage, Reported {}

    /** A sum is spread and its cases share no data to copy. */
    @Code(DiagnosticCode.E1015)
    record SpreadOfASumWhoseCasesShareNothing(String spread, String sum) implements DataMessage, Reported {}

    /** A spread supplies a field of the wrong type. */
    @Code(DiagnosticCode.E1016)
    record SpreadSuppliesTheWrongType(String field, String supplied, String type, String needed)
            implements DataMessage, Reported {}

    /** One name is written twice among a data's fields. */
    @Code(DiagnosticCode.E1011)
    record FieldIsDefinedMoreThanOnce(String field) implements DataMessage, Reported {}

    /** One name is written twice among the fields a data declares. */
    @Code(DiagnosticCode.E1011)
    record FieldIsDeclaredMoreThanOnceIn(String field, String data) implements DataMessage, Reported {}

    /** One name is listed twice where a list of names is written. */
    @Code(DiagnosticCode.E1011)
    record NameIsListedMoreThanOnce(String name, String listedIn) implements DataMessage, Reported {}

    /** A construction leaves a field of its type unwritten. */
    @Code(DiagnosticCode.E1005)
    record ConstructionIsMissingAField(String data, String field) implements DataMessage, Reported {}

    /** A construction writes a field the type does not have. */
    @Code(DiagnosticCode.E1014)
    record NotAFieldOf(String field, String data) implements DataMessage, Reported {}

    /** What to write where a construction leaves a field unwritten and nothing was spread. */
    record GiveTheFieldAValue(String field) implements DataMessage, Supporting {}

    /** What to write where a spread does not provide the missing field. */
    record SupplyTheFieldExplicitly(String field) implements DataMessage, Supporting {}

    /** The field is outside the part every case of the spread sum shares. */
    record TheFieldIsNotInWhatTheSumShares(String field, String sum) implements DataMessage, Supporting {}

    /** The field is outside the shared part of every one of the sums spread. */
    record TheFieldIsInTheSharedPartOfNoneOfThese(String field, String sums)
            implements DataMessage, Supporting {}

    /** A union written where it stands declares nothing about what its cases share. */
    record NameTheUnionWithADeclaration(String union) implements DataMessage, Supporting {}

    /**
     * A data needs a value of itself, through names with nothing to bottom out.
     *
     * <p>The first of the refusals a type with no value is given. They share a code and differ in
     * what the reading proved, which is carried with the count and read in one place: a sentence
     * chosen anywhere else would be chosen by looking at the declaration a second time, and the
     * second look is free to pick the one the count did not mean.
     */
    @Code(DiagnosticCode.E1013)
    record DataCannotBeConstructed(String data) implements DataMessage, Reported {}

    /** The rules a data states contradict, so nothing satisfies all of them. */
    @Code(DiagnosticCode.E1013)
    record ItsRulesCannotAllHold(String data) implements DataMessage, Reported {}

    /**
     * The rules leave one position no value its order holds.
     *
     * <p>{@link ItsRulesCannotAllHold} with the place filled in. The general sentence is true of
     * this and says only that something contradicts, which leaves an author reading every clause to
     * find out which position is the one — and the reading knows.
     *
     * <p>What was shown and not one of the ways of showing it. Three shapes come to this: two ends
     * that cross, one end the order does not reach, and two equalities naming different values. A
     * sentence about a pair of bounds is true of the first and sends the author of the other two
     * looking for a rule the model does not contain.
     */
    @Code(DiagnosticCode.E1013)
    record NothingIsLeftForThatPositionToHold(String data, String at)
            implements DataMessage, Reported {}

    /** A set is asked to hold more values that differ than there are of what it holds. */
    @Code(DiagnosticCode.E1013)
    record ASetCannotBeFilledFromItsElement(String data, String at, long available)
            implements DataMessage, Reported {}

    /** The rules leave a collection no size it may have. */
    @Code(DiagnosticCode.E1013)
    record NoSizeItsRulesAdmit(String data, String at) implements DataMessage, Reported {}

    /** A collection the rules will not let be empty, of something there is no value of. */
    @Code(DiagnosticCode.E1013)
    record ACollectionThatCannotBeEmptyHasNothingToHold(String data, String at)
            implements DataMessage, Reported {}

    /** Every case of a sum has no value, so the sum has none. */
    @Code(DiagnosticCode.E1013)
    record NoCaseOfItHasAValue(String data) implements DataMessage, Reported {}

    /** A data holds a type that has no value. */
    @Code(DiagnosticCode.E1013)
    record ItHoldsATypeWithNoValue(String data, String held) implements DataMessage, Reported {}

    /** What would give a self-referring data a value, where the recursion runs through a field. */
    record ItWouldHaveOneIfTheFieldCouldBeAbsent(String data, String field)
            implements DataMessage, Supporting {}

    /** The same, where it runs through a collection the rules will not let be empty. */
    record ItWouldHaveOneIfTheCollectionCouldBeEmpty(String data, String at)
            implements DataMessage, Supporting {}

    /** The same, where every case of a sum holds it. */
    record ACaseThatDoesNotHoldItWouldGiveItOne(String data) implements DataMessage, Supporting {}

    @Code(DiagnosticCode.E1010)
    record ACaseDeclaresTheDiscriminatorField(String caseName, String field, String sum) implements DataMessage, Reported {}

    record TheTagAndTheFieldWantOneKey(String field) implements DataMessage, Supporting {}

    @Code(DiagnosticCode.E1010)
    record AMemberDeclaresTheDiscriminatorField(String member, String field, String behavior) implements DataMessage, Reported {}

    @Code(DiagnosticCode.E2010)
    record TheWrittenValueViolatesTheInvariant(String value) implements DataMessage, Reported {}

    @Code(DiagnosticCode.E2010)
    record TheWrittenValueViolatesTheClause(String value, String clause) implements DataMessage, Reported {}

    @Code(DiagnosticCode.E1018)
    record ItCannotBeConstructedHere(String data) implements DataMessage, Reported {}

    @Code(DiagnosticCode.E1017)
    record AConstructionCannotBeWrittenHere(String data) implements DataMessage, Reported {}

    @Code(DiagnosticCode.E1008)
    record ADataWithAnEmptyBody(String data) implements DataMessage, Reported {}

    record WriteItAsAUnitDataOrGiveItFields(String data) implements DataMessage, Supporting {}

    @Code(DiagnosticCode.E1502)
    record ADataTakesTheStandardLibraryQualifier(String data) implements DataMessage, Reported {}

    @Code(DiagnosticCode.E1311)
    /** {@code carries} is the part of the field's type that had no external representation, which is
     *  not always the whole of it — the field is what the caret is on and the part is what has to
     *  change. */
    record NoCodecCanBeDerived(String data, String carries) implements DataMessage, Reported {}

    @Code(DiagnosticCode.E1311)
    record ATupleHasNoExternalRepresentation(String data, String carries) implements DataMessage, Reported {}

    @Code(DiagnosticCode.E1011)
    record ADataIsAlreadyDefined(String data) implements DataMessage, Reported {}

    @Code(DiagnosticCode.E1011)
    record ALetIsAlreadyDefined(String name) implements DataMessage, Reported {}

    @Code(DiagnosticCode.E1012)
    record ALetAndADataShareOneSpelling(String name) implements DataMessage, Reported {}

    @Code(DiagnosticCode.E2106)
    record AFieldTakesAMethodOfObject(String data, String field) implements DataMessage, Reported {}

    @Code(DiagnosticCode.E1311)
    record ATupleCannotBeAField(String data, String field) implements DataMessage, Reported {}

    @Code(DiagnosticCode.E1317)
    record AFieldExpectsAnotherType(String field, String expects, String got) implements DataMessage, Reported {}

    @Code(DiagnosticCode.E1802)
    record ANewtypeWrapsOneValue(String newtype, String applied) implements DataMessage, Reported {}

    @Code(DiagnosticCode.E1009)
    record ANewtypeMayNotWrapAnOptional(String newtype, String wraps) implements DataMessage, Reported {}

    record WrapTheValueAndWriteTheQuestionMarkOnTheField(String newtype) implements DataMessage, Supporting {}
}
