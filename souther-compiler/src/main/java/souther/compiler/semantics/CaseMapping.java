package souther.compiler.semantics;

import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

/**
 * What a string is made into by case conversions before it is counted, or none where it is counted
 * as it stands. A conversion of a conversion is a conversion: the outermost is the last applied.
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

    /** What {@code String.lowercase} answers of the string. */
    CaseMapping LOWERCASE = new Lowercase(NONE);

    /** What {@code String.uppercase} answers of the string. */
    CaseMapping UPPERCASE = new Uppercase(NONE);

    /** The string as it stands. */
    record None() implements CaseMapping {
    }

    /** What {@code String.lowercase} answers of what {@code of} makes of the string. */
    record Lowercase(CaseMapping of) implements CaseMapping {
    }

    /** What {@code String.uppercase} answers of what {@code of} makes of the string. */
    record Uppercase(CaseMapping of) implements CaseMapping {
    }

    /**
     * The most code points a conversion of one code point answers: the full mapping of a code
     * point is no more than three, and the form that follows composes and never lengthens.
     */
    int MOST_CODE_POINTS_OF_ONE = 3;

    /**
     * The longest text that this makes a text of no more than {@code limit} code points of,
     * whatever the text is: each conversion done answers at most {@link #MOST_CODE_POINTS_OF_ONE}
     * code points for each it was handed.
     */
    default long longestTextWithin(long limit) {
        long longest = limit;
        for (int done = operations().size(); done > 0; done--) {
            longest /= MOST_CODE_POINTS_OF_ONE;
        }
        return longest;
    }

    /** Whether {@code operation} is a case conversion. */
    static boolean isAConversion(ValueName operation) {
        return applying(operation, NONE) != null;
    }

    /** What {@code operation} makes of what {@code inner} makes of the string, or null where
     *  {@code operation} is no case conversion. */
    static CaseMapping applying(ValueName operation, CaseMapping inner) {
        if (ValueName.Stdlib.operation("String", "lowercase").equals(operation)) {
            return new Lowercase(inner);
        }
        return ValueName.Stdlib.operation("String", "uppercase").equals(operation)
                ? new Uppercase(inner) : null;
    }

    /**
     * The operations of the library this is made of, each as the library names it, the one done
     * first before the one done last: none for the string as it stands.
     */
    default List<String> operations() {
        return switch (this) {
            case None _ -> List.of();
            case Lowercase lowercase -> concat(lowercase.of().operations(),
                    ValueName.Stdlib.operation("String", "lowercase").qualified());
            case Uppercase uppercase -> concat(uppercase.of().operations(),
                    ValueName.Stdlib.operation("String", "uppercase").qualified());
        };
    }

    private static List<String> concat(List<String> before, String last) {
        List<String> out = new ArrayList<>(before);
        out.add(last);
        return List.copyOf(out);
    }

    /** {@code value} as it is written where it has been converted by this. */
    default String writtenAround(String value) {
        return switch (this) {
            case None _ -> value;
            case Lowercase lowercase -> "String.lowercase(" + lowercase.of().writtenAround(value)
                    + ")";
            case Uppercase uppercase -> "String.uppercase(" + uppercase.of().writtenAround(value)
                    + ")";
        };
    }
}
