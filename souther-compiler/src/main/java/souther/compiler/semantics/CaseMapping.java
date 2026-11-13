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
 *
 * <p>The one place that says which operations of the library are case conversions
 * ({@link #isAConversion}), and the only one a reader of a relation asks: it works with what a
 * conversion is exactly a map on ({@code regex.CodeMap}, worked out from the run time) and never
 * names an operation. A conversion added to the library is added here, with the facts about it
 * that {@link OperationFacts} states for every operation (what it keeps, how long its answer is);
 * what a relation over it comes to follows from the map and is not written again where the
 * relation is read.
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

    /** Whether {@code operation} is a case conversion. */
    static boolean isAConversion(ValueName operation) {
        return applying(operation, NONE) != null;
    }

    /**
     * What {@code operation} makes of what {@code inner} makes of the string, or null where
     * {@code operation} is no case conversion.
     *
     * <p>A conversion applied to what the same conversion made is that conversion: the run time's
     * lowercase and uppercase are each idempotent, in value and in where they stop, so
     * {@code lowercase(lowercase(x))} is the mapping {@code lowercase(x)} is. A chain of one
     * conversion is therefore one mapping however long it is, and the maps worked out for it are
     * worked out once.
     *
     * <p>Every chain therefore alternates, and a chain that alternates for long is a chain that
     * has stopped changing what it makes: see {@link #MOST_ALTERNATING_ENDING_IN_LOWERCASE}.
     */
    static CaseMapping applying(ValueName operation, CaseMapping inner) {
        if (ValueName.Stdlib.operation("String", "lowercase").equals(operation)) {
            return inner instanceof Lowercase ? inner : alternating(new Lowercase(inner));
        }
        if (ValueName.Stdlib.operation("String", "uppercase").equals(operation)) {
            return inner instanceof Uppercase ? inner : alternating(new Uppercase(inner));
        }
        return null;
    }

    /**
     * The longest chain of alternating conversions, one ending in lowercase, that is a mapping of
     * its own; a longer one makes what the chain two conversions shorter makes ({@link
     * #MOST_ALTERNATING_ENDING_IN_UPPERCASE} for one ending in uppercase). Neither is a property
     * the Unicode mappings state: it is what the run time's conversions are found to do, over every
     * code point and every pair of the code points a conversion changes, over every triple of those
     * with a mark, a widening or a context, and over millions of other triples. Shorter chains are
     * not equal to the ones two shorter — {@code lowercase(uppercase(lowercase(x)))} is not
     * {@code lowercase(uppercase(x))}: the capital sharp s is its own uppercase and not its own
     * lowercase, and the combining ypogegrammeni (U+0345) before some marks ends in different code
     * points after one more pass — so no shorter chain is shortened.
     */
    int MOST_ALTERNATING_ENDING_IN_LOWERCASE = 4;

    /** The longest chain of alternating conversions ending in uppercase that is a mapping of its
     *  own ({@link #MOST_ALTERNATING_ENDING_IN_LOWERCASE}). */
    int MOST_ALTERNATING_ENDING_IN_UPPERCASE = 3;

    /** {@code chain}, or the chain of its last conversions that makes what it makes where it is
     *  longer than a chain of its kind is a mapping of its own. */
    private static CaseMapping alternating(CaseMapping chain) {
        int most = chain instanceof Lowercase ? MOST_ALTERNATING_ENDING_IN_LOWERCASE
                : MOST_ALTERNATING_ENDING_IN_UPPERCASE;
        List<CaseMapping> done = chain.doneSoFar();
        if (done.size() <= most) {
            return chain;
        }
        // The first two conversions dropped, each of the others kept on what the one before made.
        CaseMapping kept = NONE;
        for (CaseMapping each : done.subList(2, done.size())) {
            kept = each instanceof Lowercase ? new Lowercase(kept) : new Uppercase(kept);
        }
        return kept;
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

    /**
     * Each conversion this is made of as far as it has been done, the one done first alone and
     * this whole last: the same count and order as {@link #operations}, so the operation at a
     * place is the last one done by the conversion at the same place. None for the string as it
     * stands.
     */
    default List<CaseMapping> doneSoFar() {
        List<CaseMapping> out = switch (this) {
            case None _ -> new ArrayList<>();
            case Lowercase lowercase -> new ArrayList<>(lowercase.of().doneSoFar());
            case Uppercase uppercase -> new ArrayList<>(uppercase.of().doneSoFar());
        };
        if (!(this instanceof None)) {
            out.add(this);
        }
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
