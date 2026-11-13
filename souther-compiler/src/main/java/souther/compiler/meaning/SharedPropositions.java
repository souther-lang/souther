package souther.compiler.meaning;

import java.lang.ref.WeakReference;
import java.util.Map;
import java.util.WeakHashMap;
import java.util.function.Function;
import java.util.function.Supplier;

/**
 * One object for each conjunction, disjunction and statement on an application made while it is
 * still held somewhere.
 *
 * <p>For the cost of comparing them and for nothing else. A value chosen by cases holds the
 * condition that chose it, so one statement stands inside many others, and made again each time it
 * is two equal values that a reader filing one under the other compares part by part, down every
 * condition inside. Kept here as the first one made, an equal one made afterwards is that object,
 * and the comparison stops at it. Equality is still what {@code equals} says: a proposition made
 * some other way is equal to the one kept here, and is no less a proposition for not being it.
 *
 * <p>Compared as values when one is made. Its parts made the same way are the ones kept here
 * already, so the comparison stops at each of them.
 *
 * <p>And each comparison asked for its denial, and that denial, so that equal comparisons made
 * by different readers share one denial ({@link Proposition.Compared#denied}).
 *
 * <p>Held weakly both ways. A key held weakly whose value is the key itself held strongly is never
 * let go, so what is kept is a reference to it, and one nobody else holds is let go with its
 * entry. The denial of each is the proposition's own to keep ({@link Proposition.Denial}).
 */
final class SharedPropositions {

    private static final Map<Proposition, WeakReference<Proposition>> KEPT = new WeakHashMap<>();
    /**
     * The choices each count is written out as, held as long as the count is. Held strongly: what
     * is written out names the count's statements and never the count, so it keeps nothing alive
     * that the count does not, and held weakly it was let go between one reader and the next.
     */
    private static final Map<Proposition, WhichOfThemHold.Written> CHOICES = new WeakHashMap<>();

    /**
     * The cases a statement over the ways is written out as, by what they are written out from.
     * Kept while that is held by any statement over the ways, which holds it for both the
     * statement and its denial.
     */
    private static final Map<Proposition.WaysToWrite, Proposition> WRITTEN = new WeakHashMap<>();

    /**
     * What a statement says of itself that is the same wherever it stands.
     *
     * <p>Held as long as the statement is, once for each kind of fact: a statement stands inside
     * every statement made of it, and one condition read through a name used twice is two parts of
     * what is made of it, so a reader that goes down the parts to ask pays for every way down.
     * Asked here, each statement says it once to every reader and every statement above it.
     * Held strongly: what is held names parts of the statement and never the statement.
     */
    private static final Map<Proposition, Object[]> FACTS = new WeakHashMap<>();

    /** The kinds of fact {@link #fact} keeps. */
    enum Fact {
        /** Whether some part answers only where an operation does. */
        ANSWERING,
        /** Whether it is, or holds, a search from a node for some node below it. */
        SEARCH_BELOW,
        /** Whether some part is about what a dependency answered. */
        ABOUT_AN_ANSWER,
        /** Why the first part nothing read stopped, or nothing where all were read. */
        FIRST_STOP
    }

    private SharedPropositions() {
    }

    /**
     * The fact {@code kind} of {@code stated}: worked out by {@code work} the first time it is
     * asked while {@code stated} is held, and the same after.
     *
     * <p>Worked out outside the lock, since working it out asks the same of every part. Two
     * readers asking at once work out the same, and the first is kept.
     */
    @SuppressWarnings("unchecked")
    static <T> T fact(Proposition stated, Fact kind, Function<Proposition, T> work) {
        synchronized (FACTS) {
            Object[] held = FACTS.get(stated);
            if (held != null && held[kind.ordinal()] != null) {
                return (T) held[kind.ordinal()];
            }
        }
        T made = work.apply(stated);
        synchronized (FACTS) {
            Object[] held = FACTS.computeIfAbsent(stated, _ -> new Object[Fact.values().length]);
            if (held[kind.ordinal()] == null) {
                held[kind.ordinal()] = made;
            }
            return (T) held[kind.ordinal()];
        }
    }

    /**
     * The cases written out from {@code ways}: the ones written out the first time they were asked
     * for while {@code ways} is held, or {@code writing}'s, kept from now on.
     *
     * <p>Written outside the lock, since writing them out concludes and builds every case. Two
     * readers asking at once write two equal cases and keep the first, which is the same as the
     * second: they follow from what is written out from.
     */
    static Proposition writtenOut(Proposition.WaysToWrite ways, Supplier<Proposition> writing) {
        synchronized (WRITTEN) {
            Proposition held = WRITTEN.get(ways);
            if (held != null) {
                return held;
            }
        }
        Proposition made = writing.get();
        synchronized (WRITTEN) {
            Proposition raced = WRITTEN.putIfAbsent(ways, made);
            return raced != null ? raced : made;
        }
    }

    /** The proposition equal to {@code made} that is kept, or {@code made}, kept from now on. */
    static Proposition shared(Proposition made) {
        synchronized (KEPT) {
            WeakReference<Proposition> held = KEPT.get(made);
            Proposition kept = held == null ? null : held.get();
            if (kept != null) {
                return kept;
            }
            KEPT.put(made, new WeakReference<>(made));
            return made;
        }
    }

    /**
     * The choices {@code counted} is written out as, or null where they are not: the ones written
     * out the first time they were asked for while both are held, or {@code writing}'s, kept from
     * now on.
     *
     * <p>Every reader that takes a count apart asks for them, and written out again for each, the
     * count is written out as many times as it has readers. That none could be written out is kept
     * as well, so that it is found out once.
     */
    static WhichOfThemHold.Written choices(Proposition.SoManyHold counted,
                                           Supplier<WhichOfThemHold.Written> writing) {
        synchronized (CHOICES) {
            WhichOfThemHold.Written held = CHOICES.get(counted);
            if (held != null) {
                return held;
            }
        }
        WhichOfThemHold.Written made = writing.get();
        synchronized (CHOICES) {
            CHOICES.putIfAbsent(counted, made);
        }
        return made;
    }
}
