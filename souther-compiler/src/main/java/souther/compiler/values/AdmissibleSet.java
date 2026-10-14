package souther.compiler.values;

import souther.compiler.observe.Figure;

import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Which values a position may hold, and how much of what the rules say about it was read.
 *
 * <p>Two axes and not two answers. What was found and how far the finding got are orthogonal — a
 * set of two values read in full and the same set read beside a rule this could not take in are the
 * same set — and a caller needs both to do anything with either. Written as a product so that
 * neither can be taken without the other, and so that what each combination licenses can be stated
 * once as a table rather than rediscovered at each reader:
 *
 * <pre>
 *     Finite(S),   Complete    the model divides the position into exactly these values
 *     Finite(S),   Partial     these values, and the rules may leave fewer
 *     Cofinite(E), Complete    the model excludes these and divides nothing
 *     Cofinite(E), Partial     the same, and the rules may exclude more
 *     ANY,         Complete    the model says nothing about which values stand here
 *     ANY,         Partial     this reading says nothing, which is not the model saying nothing
 * </pre>
 *
 * <p>The last row is the one the product exists for. It reads exactly like the row above it and
 * means the opposite to anyone deciding whether a position is one the model draws no distinction
 * at.
 *
 * <p>{@link #approximation} is an upper bound in every row: everything it excludes is excluded.
 * What a reader may do with it follows from that alone, and the three are deliberately not the
 * same list:
 *
 * <pre>
 *     narrow with it            in every row — a class holding none of its values holds none
 *     make classes out of it    wherever it is finite — the values are the ones the model named
 *     call it exact             only under Complete
 * </pre>
 *
 * <p>The middle one is the row to keep. A finite set read beside a rule this could not take in
 * names the same values the model singled out, and the classes are the same classes; what the
 * completeness beside it settles is what may be said about them afterwards — that a rule which went
 * unread may yet refuse one — and not whether there are any. A reading that made classes only under
 * {@code Complete} would leave the two spellings of one distinction measured differently again, the
 * sum keeping its cases beside a rule nothing could read and the enumeration losing them.
 */
public record AdmissibleSet(ValueSet approximation, Completeness completeness) {

    public AdmissibleSet {
        if (approximation == null || completeness == null) {
            throw new IllegalArgumentException("a set with no values or no account of itself");
        }
    }

    /**
     * Whether the set can be guaranteed to be what the rules leave the position, and what stands in
     * the way where it cannot.
     *
     * <p>A proof state and not a fact about the model. {@link Complete} says this reading can show
     * the equality; {@link Wider} says it cannot, which leaves open that the values happen to be
     * exact. So a sharper reading later answers {@code Complete} where this answers {@code Wider}
     * without either word changing meaning, and nothing downstream has to be told that it did.
     */
    public sealed interface Completeness {

        /** The set is what the rules leave the position, and this reading can show it. */
        record Complete() implements Completeness {}

        /**
         * The set may be wider than the rules leave the position, and these are the reasons this
         * reading cannot rule that out.
         *
         * <p>More than one at once. A rule may go unread at a position of a value whose other
         * clauses the reading also could not hold together, and the two are lifted by different
         * work — one wants a reader for a form, one wants the alternatives kept apart. Held as a
         * set so that a reader looking for either finds it, rather than finding whichever a
         * precedence put first.
         */
        record Wider(Set<Widening> why) implements Completeness {

            public Wider {
                if (why == null || why.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a reading that cannot show the equality knows what stands in the way");
                }
                // Kept in the order they were recorded rather than as an immutable copy, whose
                // iteration order is salted per run of the JVM. What is written out of these has
                // to come out the same on two compiles of one model.
                why = java.util.Collections.unmodifiableSet(new java.util.LinkedHashSet<>(why));
            }
        }
    }

    /** One thing standing between a set and the rules it is read from. */
    public sealed interface Widening {

        /**
         * A rule about the position went unread, so a value the set holds may yet be refused.
         *
         * <p>Which kind of unread it was travels with it: the three are lifted by different work
         * and a report writes its own word for each. So does the figure it stopped at, where an
         * allowance is what stopped it ({@link StoppedReading}).
         *
         * @param why    what stopped the reading
         * @param figure the figure it stopped at, or null where {@code why} carries none
         */
        record RuleUnread(UnreadReason why, Figure figure) implements Widening {

            public RuleUnread {
                if (why == null) {
                    throw new IllegalArgumentException("a rule went unread for something");
                }
                if ((figure != null) != StoppedReading.carriesAFigure(why)) {
                    throw new IllegalArgumentException(
                            "a figure is carried exactly where an allowance stopped the reading: "
                                    + why + " at " + figure);
                }
            }

            /** What stopped the reading, as a stopped reading says it. */
            public RuleUnread(StoppedReading stopped) {
                this(stopped.why(), stopped.figure());
            }

            /** What stopped the reading, with the figure beside it. */
            public StoppedReading stopped() {
                return new StoppedReading(why, figure);
            }
        }

        /**
         * Every rule was read, and the reading could not hold what they say together.
         *
         * <p>No rule is answerable for this: a choice reaching across two positions is read one
         * position at a time, so what a second clause meets it with can leave the values wider than
         * the rules are with every rule read. Beside {@link RuleUnread} and never instead of it —
         * nothing went unread, and saying so would send an author looking for a clause this
         * compiler could not take in.
         */
        record AlternativesNotSeparated() implements Widening {}

        /**
         * Every rule was read, and the set they leave between them cost more to build than this
         * compiler allows itself.
         *
         * <p>Beside {@link RuleUnread} and never instead of it, for the reason above and one more.
         * Nothing went unread — each rule was followed to the end, and where two of them came from
         * two declarations each was read in full where it was written. What was not built is the
         * set the two of them come to, and no rule is answerable for that: two patterns each small
         * on its own have a meet the size of their product. Written as a rule going unread, a
         * reader would be told to go and change one of them, which for a product of two is false of
         * each.
         */
        record ExactValuesTooCostly() implements Widening {}
    }

    /** Every rule about the position was read, which is what a reader holding no reading of its own
     * starts from. */
    public static final Completeness READ_IN_FULL = new Completeness.Complete();

    /** The whole of what the rules leave the position. */
    public static AdmissibleSet complete(ValueSet values) {
        return new AdmissibleSet(values, READ_IN_FULL);
    }

    /** These values, with something about the position left unread. */
    public static AdmissibleSet partial(ValueSet values, StoppedReading why) {
        return new AdmissibleSet(values,
                new Completeness.Wider(Set.of(new Widening.RuleUnread(why))));
    }

    /** These values, with {@code why} standing between them and the rules. */
    public static AdmissibleSet wider(ValueSet values, Set<Widening> why) {
        return new AdmissibleSet(values, new Completeness.Wider(why));
    }

    /**
     * What this and {@code other} leave one position together, so far as that can be said without
     * building anything.
     *
     * <p>For a caller holding two readings of one position — a record's rules about a field and
     * another record's about the same field — and no allowance to meet them with. A finite set is
     * kept to the values the other also has, which is exact; where neither is finite, either one
     * is still an upper bound, and the one kept is said to be wider than what the two leave
     * ({@link Widening.ExactValuesTooCostly}), since the set they leave together was not built.
     */
    public AdmissibleSet narrower(AdmissibleSet other) {
        if (other.approximation.isAny()) {
            return new AdmissibleSet(approximation, both(completeness, other.completeness));
        }
        if (approximation.isAny()) {
            return new AdmissibleSet(other.approximation, both(completeness, other.completeness));
        }
        ValueSet.Finite finite = approximation instanceof ValueSet.Finite it ? it
                : other.approximation instanceof ValueSet.Finite it ? it : null;
        if (finite == null) {
            Set<Widening> why = new LinkedHashSet<>(reasons(both(completeness,
                    other.completeness)));
            why.add(new Widening.ExactValuesTooCostly());
            return wider(approximation, why);
        }
        ValueSet against = finite == approximation ? other.approximation : approximation;
        Set<Value> kept = new LinkedHashSet<>();
        for (Value each : finite.values()) {
            if (against.has(each)) {
                kept.add(each);
            }
        }
        return new AdmissibleSet(ValueSet.oneOf(kept), both(completeness, other.completeness));
    }

    /** Read in full only where both were, and short of whatever either was short of. */
    private static Completeness both(Completeness one, Completeness other) {
        Set<Widening> why = new LinkedHashSet<>(reasons(one));
        why.addAll(reasons(other));
        return why.isEmpty() ? READ_IN_FULL : new Completeness.Wider(why);
    }

    private static Set<Widening> reasons(Completeness completeness) {
        return completeness instanceof Completeness.Wider wider ? wider.why() : Set.of();
    }

    /**
     * Whether the reading ran to the end of the rules and could not hold what they say together.
     *
     * <p>Beside {@link #whyPartial()} and answering a different question. Both leave the values an
     * upper bound this reading cannot show is what the rules leave, and what would lift them is
     * different work — so a caller deciding what to do with the set reads whether it is
     * {@link Completeness.Complete}, and one deciding what to say about it reads these.
     */
    public boolean alternativesNotSeparated() {
        return completeness instanceof Completeness.Wider wider
                && wider.why().contains(new Widening.AlternativesNotSeparated());
    }

    /**
     * Whether the reading ran to the end of the rules and the set they leave was not built.
     *
     * <p>The third of these, asked the way the one above is and for the same reason: it leaves the
     * values an upper bound, and what would lift it is neither a reader for a form nor a sharper
     * way of holding alternatives but an allowance this compiler does not give itself.
     */
    public boolean exactValuesTooCostly() {
        return completeness instanceof Completeness.Wider wider
                && wider.why().contains(new Widening.ExactValuesTooCostly());
    }

    /**
     * Which rule of the position went unread, or null where none did.
     *
     * <p>Null is not {@link Completeness.Complete}. A reading may be unable to show the equality
     * with every rule read, and a caller asking this to find out whether the set is exact would
     * read that as a complete reading — {@link #completeness} is the question, and this is only
     * what to say about the rules.
     */
    public StoppedReading whyPartial() {
        if (!(completeness instanceof Completeness.Wider wider)) {
            return null;
        }
        return wider.why().stream()
                .filter(Widening.RuleUnread.class::isInstance)
                .map(each -> ((Widening.RuleUnread) each).stopped())
                .findFirst().orElse(null);
    }
}
