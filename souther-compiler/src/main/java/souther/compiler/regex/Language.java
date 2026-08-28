package souther.compiler.regex;

/**
 * A set of strings this compiler can answer about exactly.
 *
 * <p>Every operation here is total. What a meet of two of these holds is the strings both hold, and
 * it is always a language — there is no answer saying the meet was too much work, and that is what
 * makes this a value rather than an attempt. A caller holding one may ask it anything.
 *
 * <p><b>Which is why one is not made from a pattern.</b> Whether the work of answering exactly is
 * worth doing is a question about the answer being built, not about any one pattern in it: a
 * pattern read on its own and admitted on its own is one that may still be met with another, and
 * the meet is where the cost is. So a language is compiled from the whole of what a question needs
 * at once ({@link PatternPlan}), and what comes back is either a language every operation on which
 * is affordable or nothing at all.
 *
 * <p>Nothing here is about how a language was written. Two patterns that accept the same strings are
 * the same language, and a reader asking what one holds is answered by the strings.
 */
public final class Language {

    private final Automaton machine;

    Language(Automaton machine) {
        this.machine = machine;
    }

    /** Whether the whole of {@code value} is in it. */
    public boolean has(String value) {
        return machine.accepts(value);
    }

    /** The strings both hold. */
    public Language and(Language other) {
        return new Language(machine.and(other.machine));
    }

    /** The strings either holds. */
    public Language or(Language other) {
        return new Language(machine.or(other.machine));
    }

    /** The strings this does not hold. */
    public Language not() {
        return new Language(machine.not());
    }

    /** Whether it holds nothing at all. */
    public boolean isEmpty() {
        return machine.isEmpty();
    }

    /**
     * Whether it holds every string there is.
     *
     * <p>Asked of the strings and not of how it was written. {@code .*} is not everything — the
     * five line terminators are outside it — and a reader answering from the shape of a pattern
     * would say it was.
     */
    public boolean isEverything() {
        return machine.isEverything();
    }

    /**
     * One string it holds, or null where it holds none.
     *
     * <p>Never null for a language that has something, which is what ties it to {@link #isEmpty}.
     * The shortest, and among those one a source can carry where there is one — being writable is
     * preferred and is never a condition, since what a rule admits is not narrowed by what a person
     * can paste.
     *
     * <p>A value for a row is a further question and not this one. What is wanted there is a string
     * somebody reads, and a language holds what it holds.
     */
    public String some() {
        return machine.shortest();
    }

    /** How many states hold it, which is what a caller answering for its work counts. */
    public int size() {
        return machine.size();
    }
}
