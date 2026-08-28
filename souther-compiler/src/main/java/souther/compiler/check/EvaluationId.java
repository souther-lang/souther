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
 * <p>Hashed by what it is and not by which object it is, which is a different question from
 * equality. A hash has to agree with equality one way only — two that are one hash alike — so a
 * subject told apart by identity may still be hashed by something a reading can say, and it has to
 * be: {@code Object}'s hash is drawn afresh each run, and a term carrying one of these is filed
 * under it. What is taken is where the evaluation is written and which occurrence there it is, so
 * two evaluations at one position are two hashes and the whole of it is a function of the program.
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

    @Override
    public int hashCode() {
        return java.util.Objects.hash(what, where, occurrence);
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
