package souther.compiler.check;

import souther.compiler.diag.SourcePos;

/**
 * Abandons one definition whose meaning rests on a name that denotes nothing.
 *
 * <p>It carries no diagnostic, because there is nothing left to say: the name was reported where it
 * was written, and everything that follows from it — that the type cannot be constructed, that the
 * behavior does not construct what it declared, that the body does not return what it promised — is
 * that one mistake seen from another angle.
 *
 * <p>The alternative is a check-by-check silence, one condition per consequence, each of them a place
 * to forget. This says the thing itself: the compiler does not know what this definition means, so
 * the questions about what it means have no answers. Every other definition in the module is still
 * checked, which is the point — an author fixing one name should still be told about the rest.
 */
public final class Unanswerable extends RuntimeException {

    private final transient SourcePos pos;

    public Unanswerable(SourcePos pos) {
        super("a definition whose meaning depends on a name that denotes nothing", null, false, false);
        this.pos = pos;
    }

    /** Where the name that denotes nothing was written, for a caller that wants to say which
     * definition it gave up on. */
    public SourcePos pos() {
        return pos;
    }
}
