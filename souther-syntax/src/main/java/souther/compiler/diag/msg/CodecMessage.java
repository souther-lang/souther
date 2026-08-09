package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What a written codec is told: a case it names that is not one, a shape it does not agree with,
 * and a type it is asked for where there is none. */
public sealed interface CodecMessage extends Message {

    /** The codec names a case the sum does not have. */
    @Code(DiagnosticCode.E2201)
    record NotACaseOf(String caseName, String sum) implements CodecMessage {}

    /** A case of a decoded sum has no decoder of its own. */
    @Code(DiagnosticCode.E2201)
    record CaseNeedsADecoder(String caseName) implements CodecMessage {}

    /** A case of an encoded sum has no encoder of its own. */
    @Code(DiagnosticCode.E2201)
    record CaseNeedsAnEncoder(String caseName) implements CodecMessage {}

    /** The encoder leaves one of the sum's cases out. */
    @Code(DiagnosticCode.E2201)
    record TheEncoderIsMissingACase(String sum, String caseName) implements CodecMessage {}

    /** An ISO text encoder is given something that is not a temporal value. */
    @Code(DiagnosticCode.E2201)
    record AnIsoTextEncoderTakesATemporalValue(String given) implements CodecMessage {}

    /** An optional encoder is given something that is not an optional. */
    @Code(DiagnosticCode.E2201)
    record AnOptionalEncoderTakesAnOptional(String given) implements CodecMessage {}

    /** A list encoder is given something that is not a list. */
    @Code(DiagnosticCode.E2201)
    record AListEncoderTakesAList(String given) implements CodecMessage {}

    /** A set encoder is given something that is not a set. */
    @Code(DiagnosticCode.E2201)
    record ASetEncoderTakesASet(String given) implements CodecMessage {}

    /** A map encoder is given something that is not a map. */
    @Code(DiagnosticCode.E2201)
    record AMapEncoderTakesAMap(String given) implements CodecMessage {}

    /** The element encoder does not agree with what the collection holds. */
    @Code(DiagnosticCode.E2201)
    record TheElementEncoderIsNotForTheElementType(String encoder, String elementType)
            implements CodecMessage {}

    /** A decoder builds something other than the type it is the decoder of. */
    @Code(DiagnosticCode.E2201)
    record TheDecoderBuildsAnotherType(String data, String builds) implements CodecMessage {}

    /** `T.decoder` is written for a type that has none. */
    @Code(DiagnosticCode.E2202)
    record HasNoDecoder(String data) implements CodecMessage {}

    /** `T.encode` is written for a type that has none. */
    @Code(DiagnosticCode.E2202)
    record HasNoEncoder(String data) implements CodecMessage {}
}
