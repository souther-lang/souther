package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/**
 * The rule a {@link Message} reports, read off {@link Code} where the message is declared.
 *
 * <p>A function of the message's type rather than a method on the message. A record component
 * generates an accessor, so a method here would be answerable by a value the site chose: a message
 * declaring {@code DiagnosticCode reports} once overrode the derivation outright and reported
 * whatever it was handed, past an annotation saying otherwise. Nothing a record can declare
 * overrides a static function, so the code a message reports is settled where it is declared.
 */
public final class MessageCodes {

    private MessageCodes() {
    }

    /** The rule {@code message} reports. */
    public static DiagnosticCode of(Class<?> message) {
        Code code = message.getAnnotation(Code.class);
        if (code == null) {
            throw new IllegalArgumentException("a message reports a rule, and " + message.getName()
                    + " names no code");
        }
        return code.value();
    }

    /** The rule {@code message} reports. */
    public static <M extends Message & Reported> DiagnosticCode of(M message) {
        return of(message.getClass());
    }
}
