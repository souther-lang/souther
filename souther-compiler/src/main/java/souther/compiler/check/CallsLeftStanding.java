package souther.compiler.check;

import souther.compiler.types.ReachName;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.SequencedSet;

/**
 * The calls one expansion left standing, travelling with the tree that expansion produced.
 *
 * <p>Made where the decision is. An expansion leaves a call standing because the helper it reaches
 * recurses, and a reader looking at the finished tree cannot tell such a call from one an expansion
 * was supposed to remove and did not — both are a helper applied. So the fact is carried out of the
 * expansion beside what it produced, the way {@link Expansion} carries it for a module.
 *
 * <p><b>Of one expansion and not of an inliner.</b> {@link HelperInliner#leftStanding()} answers for
 * every tree an inliner was driven over, which is the right answer to what a module has to emit and
 * the wrong one here: a second clause expanded by the same inliner would be told that a call it does
 * not contain is standing in it. What a reading asks is about the tree in its hand.
 *
 * <p>This says which calls, and nothing about whether anybody can read one. A recursive helper's
 * call standing in a behavior's rule is typed against the signature the rule's scope reaches, and
 * standing in a declaration's invariant it is typed against nothing, because what a clause is read
 * over is the declaration's fields. Which of the two a reading is, is the reading's to say
 * ({@link SecondaryClauseReading}).
 */
final class CallsLeftStanding {

    /** An expansion that left nothing standing. */
    static final CallsLeftStanding NONE = new CallsLeftStanding(new LinkedHashSet<>());

    private final SequencedSet<ReachName.Declaration> standing;

    private CallsLeftStanding(SequencedSet<ReachName.Declaration> standing) {
        this.standing = Collections.unmodifiableSequencedSet(standing);
    }

    /** What one run of an expansion left standing, taken where that run ends. */
    static CallsLeftStanding of(SequencedSet<ReachName.Declaration> met) {
        return met.isEmpty() ? NONE : new CallsLeftStanding(new LinkedHashSet<>(met));
    }

    /** The calls, in the order the expansion met them. */
    SequencedSet<ReachName.Declaration> calls() {
        return standing;
    }

    /**
     * The same calls, each reached from {@code reader}.
     *
     * <p>Asked where the tree these calls stand in is read by a module other than the one that
     * expanded it, and asked together with that tree ({@link SettledInvariant#reachedFrom}): a tree
     * that reaches a helper one way beside a set that names it another is a call this says nothing
     * about.
     */
    CallsLeftStanding reachedFrom(String reader) {
        SequencedSet<ReachName.Declaration> reached = new LinkedHashSet<>();
        for (ReachName.Declaration each : standing) {
            reached.add(each.reachedFrom(reader));
        }
        return of(reached);
    }

    /** Whether this expansion left {@code reaches} standing, which is what says a call to it is the
     *  tree the expansion meant to produce rather than one it failed to remove. */
    boolean names(ReachName.Declaration reaches) {
        return reaches != null && standing.contains(reaches);
    }

    /** Whether the expansion removed everything it met. */
    boolean leftNothing() {
        return standing.isEmpty();
    }

    /**
     * Two of these are one where they name the same calls.
     *
     * <p>Part of the answer a query gives — it travels inside {@link ExpandedClauses} — so what
     * settles it decides what downstream is asked to do again, and an answer that compared by
     * identity would be a new answer every time a module was read.
     */
    @Override
    public boolean equals(Object other) {
        return other instanceof CallsLeftStanding each && standing.equals(each.standing);
    }

    @Override
    public int hashCode() {
        return standing.hashCode();
    }

    @Override
    public String toString() {
        return standing.toString();
    }
}
