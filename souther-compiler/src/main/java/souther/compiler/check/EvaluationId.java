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
 */
final class EvaluationId {

    private final SourcePos where;
    private final String what;

    EvaluationId(String what, SourcePos where) {
        this.what = what;
        this.where = where;
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
