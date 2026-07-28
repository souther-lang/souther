package souther.compiler.diag;

/**
 * A hint line under a diagnostic (Elm's {@code Hint:}). {@code messageKey} is a catalog key resolved
 * against the selected locale; {@code args} fill its placeholders.
 */
public record Note(String messageKey, Object[] args) {

    /** What makes two notes the same note. A record compares an array component by identity, and
     * {@code args} is one, so a caller asking whether two notes say the same thing compares these. */
    public record Of(String messageKey, java.util.List<Object> args) {}

    public Of identity() {
        return new Of(messageKey, args == null ? java.util.List.of() : java.util.Arrays.asList(args));
    }
}
