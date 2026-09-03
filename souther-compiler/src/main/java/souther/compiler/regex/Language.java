package souther.compiler.regex;

/**
 * A set of strings this compiler can answer about exactly.
 *
 * <p><b>Asking is free and composing is not.</b> Everything a caller may ask one of these — whether
 * it holds a string, whether it holds nothing, whether it holds everything, whether it is the same
 * set as another — is read off the machine in front of it. What is not free is making a new
 * language out of two: a meet is the product of two machines and may be larger than this compiler
 * will build, so every way to a language takes what it is allowed and answers null past it.
 *
 * <p>Which is the one thing a caller has to hold: a language is a set and may be asked anything,
 * and putting two of them together is an operation that can decline. Written the other way round —
 * composition total, questions doing the work — the work would happen inside whichever question was
 * asked first, where there is no allowance and nobody counting.
 *
 * <p><b>And it is why one is not made from a pattern.</b> Whether the work of answering exactly is
 * worth doing is a question about the answer being built, not about any one pattern in it: a
 * pattern read on its own and admitted on its own is one that may still be met with another, and
 * the meet is where the cost is. So a language is compiled from the whole of what a question needs
 * at once ({@link PatternPlan}), and what a reading spends putting them together is held beside the
 * reading ({@code souther.compiler.values.Sets}).
 *
 * <p>Nothing here is about how a language was written. Two patterns that accept the same strings are
 * the same language, and a reader asking what one holds is answered by the strings.
 */
public final class Language {

    /**
     * The one machine that accepts these strings, which is what everything here is read off.
     *
     * <p>Canonical, and that is the type's invariant rather than a thing a caller arranges. Every
     * way to a language ends in {@link Automaton#canonical}, so two of these hold the same table
     * exactly when they hold the same strings — and the questions below are a look at what is in
     * front of them rather than a search nobody counted.
     */
    private final Automaton machine;

    Language(Automaton canonical) {
        if (canonical == null) {
            throw new IllegalArgumentException("a language is some machine");
        }
        this.machine = canonical;
    }

    /**
     * The same language, where making it canonical is within what {@code meter} allows.
     *
     * <p>Null and never a machine short of canonical. What is being decided is whether this
     * compiler can afford to answer exactly, and a half-made answer handed out is one whose next
     * question does the rest of the work somewhere nobody is counting.
     */
    private static Language canonical(Automaton made, Meter meter) {
        if (made == null) {
            return null;
        }
        Automaton one = made.canonical(meter);
        return one == null ? null : new Language(one);
    }

    /** Whether the whole of {@code value} is in it. A walk over the value, which builds nothing. */
    public boolean has(String value) {
        return machine.accepts(value);
    }

    /**
     * Every string that comes before {@code than} on the strings' own order, or null past what
     * {@code meter} allows.
     *
     * <p>The order the runtime makes and a model's {@code <} is, which is not the order the symbols
     * of a machine are in — so this is built rather than read off an alphabet, and where it is built
     * is {@link RuntimeOrder}. Metered like every other way to a language: what a caller is told
     * past the allowance is that this was not made.
     *
     * <p>Here rather than in the layer that reasons about where a language stops, because a language
     * is what this returns and a machine is what makes one. What such a caller does with it — meet
     * it, take it away, ask whether two of them are one — is what a language already answers.
     */
    public static Language before(String than, Meter meter) {
        return canonical(RuntimeOrder.before(than, meter), meter);
    }

    /**
     * Every string there is, or null past what {@code meter} allows.
     *
     * <p>Which is not what {@link #not} of nothing comes to. A machine steps over what a matcher
     * reads, and a high surrogate followed by a low one is one symbol rather than two — so there are
     * sequences of symbols no string is read as, and a complement holds them like anything else.
     * Where a caller is asking whether two languages hold the same strings, two machines that differ
     * only over those are two spellings of one answer, and this is what takes them out.
     *
     * <p>For a caller composing an answer out of complements. One asking whether a string is held
     * needs nothing of it: that walk is over the string, and a string is never read as one of them.
     */
    public static Language everyString(Meter meter) {
        return canonical(RuntimeOrder.everyString(meter), meter);
    }

    /**
     * The least string it holds, or null where it holds none and where the ones it holds have no
     * least among them.
     *
     * <p>Free, like everything else asked of one of these: read off the canonical machine, and
     * nothing is built. The two nulls are one answer here because neither is a string — a caller
     * telling them apart asks {@link #isEmpty}, which is free as well.
     *
     * <p>Not {@link #some}. That one answers with the shortest, which is a different string: a
     * language of two-letter words holds no shorter one, and which of them comes first is what this
     * is about.
     */
    public String least() {
        return RuntimeOrder.leastOf(machine);
    }

    /** The strings both hold, or null where making them ran past what {@code meter} allows. */
    public Language and(Language other, Meter meter) {
        return canonical(machine.and(other.machine, meter), meter);
    }

    /** The strings either holds, on the same terms. */
    public Language or(Language other, Meter meter) {
        return canonical(machine.or(other.machine, meter), meter);
    }

    /** The strings this does not hold, on the same terms. */
    public Language not(Meter meter) {
        return canonical(machine.not(meter), meter);
    }

    /**
     * Whether it holds nothing at all.
     *
     * <p>Read off the canonical machine: one that holds nothing is one state nothing stops at. An
     * observation, as everything below is — the walking was done where it was paid for.
     */
    public boolean isEmpty() {
        return machine.holdsNothing();
    }

    /**
     * Whether it holds every string there is.
     *
     * <p>Asked of the strings and not of how it was written. {@code .*} is not everything — the
     * five line terminators are outside it — and a reader answering from the shape of a pattern
     * would say it was. Read off the canonical machine, which for that language is the one state
     * every string stops at.
     */
    public boolean isEverything() {
        return machine.holdsEverything();
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
     * One string it holds that a source can carry, or null where it holds none such.
     *
     * <p>What a caller writing a value into a model wants, which is not {@link #some}. That answers
     * with what the language holds and prefers a written string where there is one at the same
     * length; here a string nobody can paste is not an answer, so a language of control characters
     * has one to offer and none to write.
     */
    public String someWritten() {
        return machine.shortestWritten();
    }

    /**
     * The same strings and these others, or null past what {@code meter} allows.
     *
     * <p>Takes the words themselves rather than a plan. What joining them costs is the words — a
     * set of them is a machine as big as their letters — but what the answer costs is what making
     * it canonical costs, and that is a question about the two together. So this is metered like
     * every other way to a language.
     */
    public Language with(java.util.Collection<String> words, Meter meter) {
        if (words.isEmpty()) {
            return this;
        }
        Automaton theirs = Automaton.ofWords(words, meter);
        return theirs == null ? null : canonical(machine.or(theirs, meter), meter);
    }

    /** The same strings less these, on the same terms. */
    public Language without(java.util.Collection<String> words, Meter meter) {
        if (words.isEmpty()) {
            return this;
        }
        Automaton theirs = Automaton.ofWords(words, meter);
        Automaton left = theirs == null ? null : theirs.not(meter);
        return left == null ? null : canonical(machine.and(left, meter), meter);
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
     * <p><b>A comparison of two tables and not a proof about two languages.</b> Every language holds
     * the one machine that accepts its strings ({@link Automaton#canonical}), so two that hold the
     * same strings hold the same table, state for state. Which matters because of who calls this: a
     * set adding a member calls it, and a map looking one up calls it, and neither of them is a
     * place where an answer may go and build automata. The work that settles what a language is was
     * done where it was paid for.
     */
    @Override
    public boolean equals(Object other) {
        if (this == other) {
            return true;
        }
        return other instanceof Language it && machine.sameAs(it.machine);
    }

    /**
     * Read off the same table, so that two equal languages hash alike.
     *
     * <p>The strings are what makes two of these equal, and the canonical machine is what makes the
     * strings something a hash can be read off: one language is one table, so hashing the table
     * hashes the language.
     */
    @Override
    public int hashCode() {
        return machine.shape();
    }

    /**
     * The whole of what this language is, written out for a caller putting several of them in an
     * order.
     *
     * <p>Agrees with {@link #equals} both ways, being read off the same canonical table, and unlike
     * {@link #hashCode} it says which of two unequal ones comes first without ever saying that of
     * two equal ones. Costs nothing to ask: the machine it reads was built when the language was.
     */
    public void writtenInto(StringBuilder out) {
        machine.writtenInto(out);
    }

    @Override
    public String toString() {
        String some = some();
        return "language of " + (some == null ? "nothing" : "\"" + some + "\" and such");
    }
}
