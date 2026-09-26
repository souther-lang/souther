package souther.compiler.core;

import souther.compiler.abort.AbortKind;
import souther.compiler.abort.AbortSet;

import java.util.EnumMap;
import java.util.Map;

/**
 * Every kernel's {@link KernelContract}, total over {@link Kernel} the way {@link KernelSignatures}
 * already is.
 *
 * <p>Built from a {@link KernelSignatures} and nothing else — never from a second map a caller
 * supplies. {@code aborts} is answered by {@link #abortsOf}, one function this compiler owns and
 * switches over every {@link Kernel} with no default arm, so a kernel {@link Kernel#values()} adds
 * stops the build here until it is given an answer. That is what keeps this from becoming the
 * second registry {@link KernelSignatures} and a hand-kept {@code KernelAborts} would have been: the
 * abort semantics are authored once, in this one exhaustive switch, not read from a map that could
 * hold fewer entries than the kernels there are.
 */
public final class KernelContracts {

    private final Map<Kernel, KernelContract> declared;

    private KernelContracts(Map<Kernel, KernelContract> declared) {
        this.declared = declared;
    }

    /** Every kernel {@code signatures} declares, paired with what this compiler answers for
     *  {@link #abortsOf}. Total because {@code signatures} already is and {@link #abortsOf} is
     *  exhaustive by construction — there is no partial state to reject a caller's map for. */
    public static KernelContracts of(KernelSignatures signatures) {
        Map<Kernel, KernelContract> declared = new EnumMap<>(Kernel.class);
        for (Kernel kernel : Kernel.values()) {
            declared.put(kernel, new KernelContract(signatures.signatureOf(kernel), abortsOf(kernel)));
        }
        return new KernelContracts(Map.copyOf(declared));
    }

    /** {@code kernel}'s contract. Never null: the language names a fixed set of kernels and a
     *  snapshot holding fewer cannot be made, the same guarantee {@link KernelSignatures} gives. */
    public KernelContract contractOf(Kernel kernel) {
        return declared.get(kernel);
    }

    /**
     * Every {@link AbortKind} a call to {@code kernel} can end without a value for, traced against
     * {@code souther-runtime}'s implementation of it and the specification law each site cites.
     *
     * <p>One member for an operation only where the runtime it names can actually raise it — a
     * kernel typed over more than one primitive (comparison and arithmetic on collections read {@code
     * Int}, {@code Decimal} and {@code Rational} elements alike, say) answers with the union over
     * every primitive it can be instantiated at, because one {@link Kernel} names one operation
     * whichever primitive a call resolves it to.
     *
     * <p>No default arm. A kernel {@link Kernel#values()} names and this does not answer for fails
     * the build rather than silently inheriting {@link AbortSet#NONE} — which is exactly the
     * "nothing said" state a hand-kept table cannot be told apart from a considered "never aborts".
     */
    private static AbortSet abortsOf(Kernel kernel) {
        return switch (kernel) {
            // Every read, search, and case-answering operation the library states no abort for.
            case STRING_LENGTH, STRING_TO_INT, STRING_TO_DECIMAL, STRING_TRIM, STRING_LOWERCASE,
                    STRING_UPPERCASE, STRING_CONTAINS, STRING_STARTS_WITH, STRING_ENDS_WITH,
                    STRING_MATCHES, STRING_APPEND, STRING_SPLIT, STRING_JOIN, STRING_REPLACE,
                    STRING_WORDS, STRING_FROM_INT, STRING_CONCAT, STRING_REVERSE, STRING_LINES,
                    STRING_CHARACTERS, STRING_CODE_POINTS,
                    MAP_EMPTY, MAP_GET, MAP_CONTAINS_KEY, MAP_KEYS, MAP_VALUES, MAP_SINGLETON,
                    MAP_INSERT, MAP_REMOVE, MAP_IS_EMPTY, MAP_SIZE, MAP_TO_LIST, MAP_FROM_LIST,
                    LIST_LENGTH, LIST_FIND, LIST_SORT_BY, LIST_MAX, LIST_MIN, LIST_GET, LIST_REVERSE,
                    LIST_SORT,
                    SET_EMPTY, SET_SINGLETON, SET_INSERT, SET_REMOVE, SET_CONTAINS, SET_UNION,
                    SET_INTERSECTION, SET_DIFFERENCE, SET_IS_EMPTY, SET_SIZE, SET_TO_LIST,
                    SET_FROM_LIST,
                    DATE_DAYS_BETWEEN, DATE_YEAR, DATE_MONTH, DATE_DAY, DATE_FROM_PARTS,
                    TIME_FROM_PARTS, TIME_HOUR, TIME_MINUTE, TIME_SECOND,
                    DATETIME_MINUTES_BETWEEN, DATETIME_TO_DATE, DATETIME_TO_TIME,
                    DATETIME_FROM_DATE_AND_TIME,
                    INT_TRUNCATING_REMAINDER, INT_COMPARE,
                    DECIMAL_COMPARE, DECIMAL_FROM_INT,
                    RATIONAL_FROM_INT, RATIONAL_FROM_DECIMAL,
                    RATIONAL_COMPARE,
                    OPTION_MAP ->
                    AbortSet.NONE;

            // `slice`'s bounds may name nothing to slice at all (spec §stdlib-string, ADR-0096) —
            // told apart from an answer with no place, below, because these fail before any answer
            // is computed.
            case STRING_SLICE -> AbortSet.of(AbortKind.INVALID_BOUNDS);

            // The law `an-operation-refuses-only-what-its-own-answer-has-no-place-for`: "its own
            // answer, or a form the operation is defined as, has no representation". A `repeat` or
            // `pad` count no `String` could hold, a `fromDecimal` text no `String` could hold (a
            // scale far enough from nought either way), a calendar shift off the end of what a temporal
            // holds, a `List.rangeInclusive` span longer than a `List` can hold, and an `Int` or
            // `Decimal` arithmetic result outside what its type holds are the first half — the
            // answer itself has no place. `Rational.toWholeNumber`/`toInt`/`toFiniteDecimal`/
            // `toDecimal` narrowing to a carrier that holds no such value are the same half, read
            // off `Rational#asWholeNumber`/`#asDecimal`. `RATIONAL_ADD`/`SUBTRACT` are the second
            // half: the exact sum or difference always has a value, but writing it is what
            // `Rational`'s own arithmetic is defined to do — a common exponent brought out and the
            // remaining distance built in full (`Rational#plus`/`#minus`) — and that required form
            // can ask for an exponent past what `Rational` holds even where the mathematical answer
            // would fit.
            case STRING_REPEAT, STRING_PAD_LEFT, STRING_PAD_RIGHT, STRING_FROM_DECIMAL,
                    LIST_SUM, LIST_PRODUCT, LIST_RANGE_INCLUSIVE,
                    DATE_ADD_DAYS, DATE_ADD_MONTHS, DATE_ADD_YEARS,
                    DATETIME_ADD_MINUTES, DATETIME_ADD_HOURS, DATETIME_ADD_DAYS,
                    INT_ADD, INT_SUBTRACT, INT_MULTIPLY,
                    DECIMAL_TO_INT, DECIMAL_ROUND, DECIMAL_ADD, DECIMAL_SUBTRACT, DECIMAL_MULTIPLY,
                    RATIONAL_TO_WHOLE_NUMBER, RATIONAL_TO_FINITE_DECIMAL, RATIONAL_TO_INT,
                    RATIONAL_TO_DECIMAL, RATIONAL_ADD, RATIONAL_SUBTRACT, RATIONAL_MULTIPLY ->
                    AbortSet.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE);

            // `floorMod` aborts on a zero divisor like `/` does (spec §stdlib-int) and never
            // overflows: its answer is bounded by the divisor's own magnitude.
            case INT_FLOOR_MOD -> AbortSet.of(AbortKind.DIVISION_BY_ZERO);

            // `truncatingDivide` answers `DivisionByZero` as a case and aborts only on the one pair
            // whose quotient no `Int` holds (spec §stdlib-int); `Decimal.divide` answers a zero
            // divisor as a case the same way and aborts only where the quotient it rounds to has no
            // place at the scale asked (spec §stdlib-decimal).
            case INT_TRUNCATING_DIVIDE, DECIMAL_DIVIDE ->
                    AbortSet.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE);

            // The exact `/` operator: a zero divisor aborts outright (spec §stdlib-rational), and
            // the exact arithmetic underneath can still ask for an exponent past what a `Rational`
            // holds — the same law the narrowings above answer to.
            case RATIONAL_DIVIDE ->
                    AbortSet.of(AbortKind.DIVISION_BY_ZERO, AbortKind.REQUIRED_FORM_HAS_NO_PLACE);
        };
    }
}
