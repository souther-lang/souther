package souther.compiler.meaning;

import java.lang.ref.WeakReference;
import java.util.Map;
import java.util.WeakHashMap;
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
 * <p>And the denial of each, made once. A condition is stated where it holds and denied where it
 * does not, so a statement kept here is denied again wherever it is read, and a denial made afresh
 * writes out every part again before it comes to the one kept.
 *
 * <p>Held weakly both ways. A key held weakly whose value is the key itself held strongly is never
 * let go, so what is kept is a reference to it, and one nobody else holds is let go with its
 * entry. A statement and its denial are each the other's, so a denial held strongly would hold its
 * statement, and neither would be let go.
 */
final class SharedPropositions {

    private static final Map<Proposition, WeakReference<Proposition>> KEPT = new WeakHashMap<>();
    private static final Map<Proposition, WeakReference<Proposition>> DENIED =
            new WeakHashMap<>();
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

    private SharedPropositions() {
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
    /**
     * What holds exactly where {@code stated} does not: the one made the first time it was asked
     * while both are held, or {@code denying}'s, kept from now on.
     *
     * <p>And {@code stated} kept as the denial of what is made, where nothing is kept as that
     * yet: {@code stated} holds exactly where its denial does not. Made again from the denial's
     * parts, the denial of a denial would be joined from them and may be written another way —
     * a statement saying what {@code stated} says and spelled otherwise — where a reader naming
     * one column by a statement and its denial asks either of them which spells first.
     *
     * <p>Made outside the lock, since making it asks for the denial of every part. Two readers
     * asking at once make two equal denials and keep the one {@link #shared} hands both.
     */
    static Proposition denied(Proposition stated, Supplier<Proposition> denying) {
        synchronized (DENIED) {
            WeakReference<Proposition> held = DENIED.get(stated);
            Proposition kept = held == null ? null : held.get();
            if (kept != null) {
                return kept;
            }
        }
        Proposition made = denying.get();
        synchronized (DENIED) {
            WeakReference<Proposition> raced = DENIED.get(stated);
            Proposition first = raced == null ? null : raced.get();
            if (first != null) {
                return first;
            }
            DENIED.put(stated, new WeakReference<>(made));
            WeakReference<Proposition> back = DENIED.get(made);
            if (back == null || back.get() == null) {
                DENIED.put(made, new WeakReference<>(stated));
            }
        }
        return made;
    }
}
