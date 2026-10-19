package souther.compiler.semantics;

import souther.compiler.types.ValueName;

/**
 * The case conversion a string is counted through, or none where it is counted as it stands.
 *
 * <p>What a conversion answers is the run time's: the full Unicode mapping and then NFC, so the
 * code points of the answer are not a code-point-wise image of the code points it was given — a
 * letter followed by a combining mark may compose into one that no class of the letter holds. A
 * count of the answer is therefore asked of the answer and never taken back to the code points of
 * the string it was made from; what a conversion makes of a text is worked out where the run
 * time's operations are applied ({@code evaluate.BoundUnderEvaluation#mapped}).
 */
public sealed interface CaseMapping {

    /** The string as it stands. */
    CaseMapping NONE = new None();

    /** What {@code String.lowercase} answers of it. */
    CaseMapping LOWERCASE = new Lowercase();

    /** What {@code String.uppercase} answers of it. */
    CaseMapping UPPERCASE = new Uppercase();

    /** The string as it stands. */
    record None() implements CaseMapping {
    }

    /** What {@code String.lowercase} answers of the string. */
    record Lowercase() implements CaseMapping {
    }

    /** What {@code String.uppercase} answers of the string. */
    record Uppercase() implements CaseMapping {
    }

    /** The conversion {@code operation} is, or null where it is no case conversion. */
    static CaseMapping of(ValueName operation) {
        if (ValueName.Stdlib.operation("String", "lowercase").equals(operation)) {
            return LOWERCASE;
        }
        return ValueName.Stdlib.operation("String", "uppercase").equals(operation)
                ? UPPERCASE : null;
    }

    /** {@code value} as it is written where it has been converted by this. */
    default String writtenAround(String value) {
        return switch (this) {
            case None _ -> value;
            case Lowercase _ -> "String.lowercase(" + value + ")";
            case Uppercase _ -> "String.uppercase(" + value + ")";
        };
    }
}
