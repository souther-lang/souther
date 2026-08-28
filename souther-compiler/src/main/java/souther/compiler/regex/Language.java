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

    /**
     * The same strings and these others.
     *
     * <p>Takes the words themselves rather than a plan, and needs no allowance to do it. What it
     * costs is the words: a set of them is a machine as big as their letters, and joining one to
     * this is the cheap operation. So a caller holding a language and a handful of values it must
     * also admit is answered without going back for anything.
     */
    public Language with(java.util.Collection<String> words) {
        return words.isEmpty() ? this : new Language(machine.or(Automaton.ofWords(words)));
    }

    /** The same strings less these, on the same terms. */
    public Language without(java.util.Collection<String> words) {
        return words.isEmpty() ? this
                : new Language(machine.and(Automaton.ofWords(words).not()));
    }

    /** How many states hold it, which is what a caller answering for its work counts. */
    public int size() {
        return machine.size();
    }

    /**
     * Whether the two hold the same strings.
     *
     * <p>The strings and not the states. A language is a set, and two patterns that accept the same
     * strings are one — so a reading run twice over one model has to come to values that are equal,
     * whatever shape the machines took on the way.
     *
     * <p>Asked as neither holding anything the other does not, which is what sameness is and what it
     * costs. Cheap where the two are the same object, which is what a reading comparing what it just
     * built with what it had usually has.
     */
    @Override
    public boolean equals(Object other) {
        if (this == other) {
            return true;
        }
        if (!(other instanceof Language it)) {
            return false;
        }
        return machine.and(it.machine.not()).isEmpty()
                && it.machine.and(machine.not()).isEmpty();
    }

    /**
     * The same for every language, which is what a set with no cheap canonical form has.
     *
     * <p>A value's hash has to agree with its equality, and what makes two languages equal is a
     * question about their strings — there is no small thing to read off a machine that two equal
     * languages are bound to share. So they all hash alike and a table holding several of them
     * compares them; a table holding one, which is what a position's rules come to, does not
     * notice.
     */
    @Override
    public int hashCode() {
        return Language.class.hashCode();
    }

    @Override
    public String toString() {
        String some = some();
        return "language of " + (some == null ? "nothing" : "\"" + some + "\" and such");
    }
}
