package souther.compiler.diag;

import java.util.Arrays;

/**
 * A message argument that is itself localized at render time. A throw site has no locale, so a
 * sub-phrase that must follow the reader's language — a token category like "a name", not a literal
 * symbol like {@code `:`} — is passed as a {@code Localizable} and resolved by {@link Messages#get}
 * against the selected locale before it is substituted into the surrounding message.
 *
 * <p>Two phrases are equal when they name one entry with equal arguments. The arguments are an
 * array, which a record compares by identity, so equality is spelled out here: a message carrying a
 * phrase is a value, and two messages saying the same thing are equal.
 */
public record Localizable(String key, Object[] args) {

    public static Localizable of(String key, Object... args) {
        return new Localizable(key, args);
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof Localizable that && key.equals(that.key)
                && Arrays.deepEquals(args, that.args);
    }

    @Override
    public int hashCode() {
        return 31 * key.hashCode() + Arrays.deepHashCode(args);
    }

    @Override
    public String toString() {
        return key + Arrays.deepToString(args);
    }
}
