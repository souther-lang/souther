package souther.compiler.check;

import souther.compiler.diag.SourcePos;

/**
 * One evaluation the check reads, told apart from every other.
 *
 * <p>Equality is identity, and that is the whole of it. Two of these are the same evaluation when
 * they are the same object, so there is no way to spell one that equals another — which is what a
 * subject for a value nothing may share has to be. A record over the position would not do it: a
 * position says where something is written, and the same line evaluated in two places is two values
 * ({@link Location} states the same rule for bindings, and {@code an offset is not an identity} is
 * how it was learned).
 *
 * <p>Made once per occurrence and handed back, by {@link Terms#evaluationIdOf}. Constructed rather
 * than worked out again at each ask: a subject recomputed from what a walk happens to hold is a
 * subject that moves when the walk does, and a fact filed under the old one is then about nothing.
 *
 * <p>The position it carries is for a reader and takes no part in telling two apart.
 *
 * <p>What a term carrying one of these is hashed from is not which object it is. {@code Object}'s
 * hash is drawn afresh each run, and a term filed under one would be filed somewhere else the next
 * time — so the term algebra reads what was written and which occurrence of the reading this is
 * ({@code Term.STANDS_FOR}), which agrees with equality the one way a hash has to: two that are one
 * hash alike.
 *
 * <p>Named there rather than answered here. A type answering with a hash of its own is where the
 * walk that proves a term is hashed from values has to stop, and what that hash reads is then the
 * one thing nothing checks; a type naming what stands for it is walked through like everything
 * else. Which is why the position is not among what is named: it stands on a {@link
 * souther.compiler.diag.Placement}, and what that reads is a tree, not a value this can answer for.
 */
final class EvaluationId {

    private final SourcePos where;
    private final String what;

    /** Which one this is of the evaluations its reading has named, in the order it named them. */
    private final int occurrence;

    EvaluationId(String what, SourcePos where, int occurrence) {
        this.what = what;
        this.where = where;
        this.occurrence = occurrence;
    }

    /** What was written where this stands. */
    String what() {
        return what;
    }

    /** Which one this is of the evaluations its reading has named. */
    int occurrence() {
        return occurrence;
    }

    SourcePos where() {
        return where;
    }

    String rendered() {
        return "<" + what + " at "
                + (where == null ? "?" : where.line() + ":" + where.column()) + ">";
    }

    @Override
    public String toString() {
        return rendered();
    }
}
