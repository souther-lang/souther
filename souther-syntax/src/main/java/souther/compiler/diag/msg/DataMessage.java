package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What a `data` declaration and a construction of one are told. */
public sealed interface DataMessage extends Message {

    /** Two spreads, or a spread and the declaration itself, supply one field name. */
    @Code(DiagnosticCode.E1004)
    record SpreadFieldCollision(String field, String from, String heldBy) implements DataMessage {}

    /** What is spread is not a product data. */
    @Code(DiagnosticCode.E1015)
    record SpreadIsNotAProductData(String spread) implements DataMessage {}

    /** What is spread in a construction is neither a data value nor a sum whose cases agree. */
    @Code(DiagnosticCode.E1015)
    record SpreadIsNotADataValue(String spread) implements DataMessage {}

    /** A sum is spread and its cases share no data to copy. */
    @Code(DiagnosticCode.E1015)
    record SpreadOfASumWhoseCasesShareNothing(String spread, String sum) implements DataMessage {}

    /** A spread supplies a field of the wrong type. */
    @Code(DiagnosticCode.E1016)
    record SpreadSuppliesTheWrongType(String field, String supplied, String type, String needed)
            implements DataMessage {}

    /** One name is written twice among a data's fields. */
    @Code(DiagnosticCode.E1011)
    record FieldIsDefinedMoreThanOnce(String field) implements DataMessage {}

    /** One name is written twice among the fields a data declares. */
    @Code(DiagnosticCode.E1011)
    record FieldIsDeclaredMoreThanOnceIn(String field, String data) implements DataMessage {}

    /** One name is listed twice where a list of names is written. */
    @Code(DiagnosticCode.E1011)
    record NameIsListedMoreThanOnce(String name, String listedIn) implements DataMessage {}

    /** A construction leaves a field of its type unwritten. */
    @Code(DiagnosticCode.E1005)
    record ConstructionIsMissingAField(String data, String field) implements DataMessage {}

    /** A construction writes a field the type does not have. */
    @Code(DiagnosticCode.E1014)
    record NotAFieldOf(String field, String data) implements DataMessage {}

    /** What to write where a construction leaves a field unwritten and nothing was spread. */
    @Code(DiagnosticCode.E1005)
    record GiveTheFieldAValue(String field) implements DataMessage {}

    /** What to write where a spread does not provide the missing field. */
    @Code(DiagnosticCode.E1005)
    record SupplyTheFieldExplicitly(String field) implements DataMessage {}

    /** The field is outside the part every case of the spread sum shares. */
    @Code(DiagnosticCode.E1005)
    record TheFieldIsNotInWhatTheSumShares(String field, String sum) implements DataMessage {}

    /** The field is outside the shared part of every one of the sums spread. */
    @Code(DiagnosticCode.E1005)
    record TheFieldIsInTheSharedPartOfNoneOfThese(String field, String sums)
            implements DataMessage {}

    /** A union written where it stands declares nothing about what its cases share. */
    @Code(DiagnosticCode.E1015)
    record NameTheUnionWithADeclaration(String union) implements DataMessage {}

    /** A data reaches itself through a field that is always there, so none of it can be built. */
    @Code(DiagnosticCode.E1013)
    record DataCannotBeConstructed(String data) implements DataMessage {}
}
