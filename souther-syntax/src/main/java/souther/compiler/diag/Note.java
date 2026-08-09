package souther.compiler.diag;

import souther.compiler.diag.msg.Message;

/**
 * A hint line under a diagnostic (Elm's {@code Hint:}).
 *
 * <p>A hint says what to write instead, and it says it about values of its own — which is why it is
 * a {@link Message} like the line above it rather than a share of that line's values. {@code said}
 * carries it. {@code messageKey} and {@code args} are the form a site not yet migrated writes, where
 * the key is a catalog key and the arguments fill its numbered placeholders.
 */
public record Note(String messageKey, Object[] args, Message said) {

    /** A hint written as a message. */
    public Note(Message said) {
        this(said.entry(), new Object[0], said);
    }

    /** A hint written as a key and its arguments. */
    public Note(String messageKey, Object[] args) {
        this(messageKey, args, null);
    }

    /** What makes two notes the same note. A record compares an array component by identity, and
     * {@code args} is one, so a caller asking whether two notes say the same thing compares these. */
    public record Of(String messageKey, java.util.List<Object> args, Message said) {}

    public Of identity() {
        return new Of(messageKey, args == null ? java.util.List.of() : java.util.Arrays.asList(args),
                said);
    }
}
