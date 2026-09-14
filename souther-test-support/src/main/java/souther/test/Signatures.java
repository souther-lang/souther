package souther.test;

import java.lang.classfile.Signature;
import java.lang.constant.ClassDesc;

/** What a class file says a type is, written out for a reader of a failure. */
public final class Signatures {

    private Signatures() {
    }

    /** The internal name of a class type, as a class file spells it. */
    public static String named(Signature.ClassTypeSig of) {
        String descriptor = of.classDesc().descriptorString();
        return descriptor.substring(1, descriptor.length() - 1);
    }

    /** {@code of}, as a failure would name it. */
    public static String shown(Signature of) {
        return switch (of) {
            case Signature.ArrayTypeSig array -> shown(array.componentSignature()) + "[]";
            case Signature.BaseTypeSig base ->
                    ClassDesc.ofDescriptor(String.valueOf(base.baseType())).displayName();
            case Signature.TypeVarSig var -> var.identifier();
            case Signature.ClassTypeSig cls -> cls.typeArgs().isEmpty() ? named(cls)
                    : named(cls) + "<" + String.join(", ",
                            cls.typeArgs().stream().map(Signatures::shown).toList()) + ">";
        };
    }

    private static String shown(Signature.TypeArg arg) {
        return switch (arg) {
            case Signature.TypeArg.Unbounded _ -> "?";
            case Signature.TypeArg.Bounded bounded -> switch (bounded.wildcardIndicator()) {
                case NONE -> shown(bounded.boundType());
                case EXTENDS -> "? extends " + shown(bounded.boundType());
                case SUPER -> "? super " + shown(bounded.boundType());
            };
        };
    }
}
