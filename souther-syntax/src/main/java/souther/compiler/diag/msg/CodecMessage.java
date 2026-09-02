package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What a written codec is told: a shape it does not agree with, and a type it is asked for where
 * there is none. */
public sealed interface CodecMessage extends Message {

    /** An ISO text encoder is given something that is not a temporal value. */
    @Code(DiagnosticCode.E2201)
    record AnIsoTextEncoderTakesATemporalValue(String given) implements CodecMessage, Reported {}

    /** An optional encoder is given something that is not an optional. */
    @Code(DiagnosticCode.E2201)
    record AnOptionalEncoderTakesAnOptional(String given) implements CodecMessage, Reported {}

    /** A list encoder is given something that is not a list. */
    @Code(DiagnosticCode.E2201)
    record AListEncoderTakesAList(String given) implements CodecMessage, Reported {}

    /** A set encoder is given something that is not a set. */
    @Code(DiagnosticCode.E2201)
    record ASetEncoderTakesASet(String given) implements CodecMessage, Reported {}

    /** A map encoder is given something that is not a map. */
    @Code(DiagnosticCode.E2201)
    record AMapEncoderTakesAMap(String given) implements CodecMessage, Reported {}

    /** The element encoder does not agree with what the collection holds. */
    @Code(DiagnosticCode.E2201)
    record TheElementEncoderIsNotForTheElementType(String encoder, String elementType)
            implements CodecMessage, Reported {}

    /** A decoder builds something other than the type it is the decoder of. */
    @Code(DiagnosticCode.E2201)
    record TheDecoderBuildsAnotherType(String data, String builds) implements CodecMessage, Reported {}

}
