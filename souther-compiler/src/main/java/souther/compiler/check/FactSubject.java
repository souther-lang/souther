package souther.compiler.check;

/**
 * What a fact is about: the subject a constraint, a predicate or a clause is read against.
 *
 * <p>Apart from {@link Term}, which is what a value is <em>built like</em>. The two were one, and
 * {@link Term} said so of itself — "the identity two writings of one value share" — which folds two
 * questions into one answer. Whether this check can name a value at all, and whether two writings of
 * it are one value, are separate: a term is equal to its twin structurally, so anything given a term
 * is thereby declared shareable, and a value that is nameable but not shareable had nowhere to be.
 * That is why a call to a {@code behavior} was named by nothing rather than named by itself — the
 * only constructor of a name for a call ({@code Term.Interner#called}) interns on the callee and the
 * arguments, so giving one a name would have claimed that two asks answer alike.
 *
 * <p>So the order is: a value gets a subject because it can be pointed at, and two subjects are one
 * because something makes them one. Sharing is decided where a subject is built ({@link Terms#subjectOf})
 * and nowhere else, so no reader of a fact has a second question to ask about the subject it was
 * handed. A reader that re-decided it would be a reader that can forget to.
 */
sealed interface FactSubject {

    /** What to call this where a message names it. For a reader, not for equality. */
    String rendered();

    /**
     * A value named by the way it is built, and one with every other value built that way.
     *
     * <p>This is the shareable case, and it is shareable because {@link Term} is structural: a
     * location, arithmetic over locations, a call to something referentially transparent. Two
     * writings of it are one subject without anything being asked, which is what makes a guard on
     * one a guard on the other.
     */
    record OfATerm(Term term) implements FactSubject {

        public OfATerm {
            java.util.Objects.requireNonNull(term, "a subject is something to point at");
        }

        @Override
        public String rendered() {
            return term.rendered();
        }
    }

    /**
     * One evaluation, and no other — including another evaluation written the same way.
     *
     * <p>For a value that can be pointed at but not shared. What an injected behavior answers is
     * this: {@code external(id)} written twice is two asks of the outside world and so two values,
     * and a fact taken from one of them is not a fact about the other. Under one subject apiece
     * there is nothing wrong with saying either.
     *
     * <p>Which is why effects do not decide whether a value has a subject. They decide whether two
     * subjects are one. Reading them as the first is what left a whole class of values with no
     * subject at all, and a construction built from one of those was never checked and never
     * reported (#819).
     */
    record OfAnEvaluation(EvaluationId where) implements FactSubject {

        public OfAnEvaluation {
            java.util.Objects.requireNonNull(where, "an evaluation is somewhere it happened");
        }

        @Override
        public String rendered() {
            return where.rendered();
        }
    }

    /** The subject a value built like {@code term} is. Null in, null out, so a caller with nothing
     * to name stays a caller with nothing to name. */
    static FactSubject of(Term term) {
        return term == null ? null : new OfATerm(term);
    }
}
