package souther.compiler.types;

/**
 * A case the language itself gives, and the whole of the list.
 *
 * <p>These are named because a name a pattern writes has to denote something, and no source
 * declares them: there is no {@code data} anywhere that says what {@code DivisionByZero} is, and a
 * compilation that declares nothing at all still has it. That is what tells them from the standard
 * library's own declarations, which a {@code .sou} of the library writes and which are declarations
 * like any other.
 *
 * <p>Closed, and an enum for that reason. What used to stand here was a string paired with a module
 * name no module has, so {@code OfLanguage("Typo")} was a value the type admitted and nothing
 * refused. The set is small and the language settles it; a spelling is what one is written as and
 * is read off the identity, never the other way round.
 *
 * <p>Whether one of these is represented by a class is a backend's question and is not asked here.
 * Two of them are not — an {@code Option} match dispatches on the runtime {@code Option} classes and
 * never on the arm's own name — and the JVM answers for the other four; both facts live in
 * {@code jvm.SoutherJvmAbi}.
 */
public enum LanguageCaseId {

    /** {@code Some}, written in a match arm over an {@code Option}. */
    SOME("Some"),

    /** {@code None}, the same. */
    NONE("None"),

    /** What an integer or decimal division answers where the divisor is zero. */
    DIVISION_BY_ZERO("DivisionByZero"),

    /** What a decimal operation answers where the result is not a number. */
    NOT_A_NUMBER("NotANumber"),

    /** What building a date from parts answers where the parts name no date. */
    NOT_A_DATE("NotADate"),

    /** The same, for a time. */
    NOT_A_TIME("NotATime");

    private final String spelling;

    LanguageCaseId(String spelling) {
        this.spelling = spelling;
    }

    /** How this is written. One table, read forwards by everything that shows a name and backwards
     *  by {@link #named}, so a spelling can only be wrong here by being wrong in both directions. */
    public String spelling() {
        return spelling;
    }

    /** The case written {@code spelling}, or null where none is. */
    public static LanguageCaseId named(String spelling) {
        for (LanguageCaseId id : values()) {
            if (id.spelling.equals(spelling)) {
                return id;
            }
        }
        return null;
    }
}
