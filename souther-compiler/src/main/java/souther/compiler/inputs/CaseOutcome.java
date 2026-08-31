package souther.compiler.inputs;

/**
 * What became of one case of a sum when the reading reached it.
 *
 * <p>Every case of every sum the walk met has exactly one of these, which is what lets a reader ask
 * whether a sum has a value at all: a sum stands wherever any of its cases does, so the question is
 * answered over the whole list or it is not answered.
 *
 * <p><b>Two of these are facts about the model and two are not.</b> That naming a case builds it,
 * and that the rules leave nothing at one, are what the declarations say. That a reading was opened
 * under a case, and that this walk did not go down one, are facts about this reading — and the
 * second of those is the one a reader must not take for the first kind. A case this walk never
 * entered has not been shown to hold nothing; it has not been shown anything, and a proof built from
 * it would say a model has no value because this compiler stopped looking.
 */
sealed interface CaseOutcome {

    /**
     * A reading of the case was opened, and stands at {@code at}.
     *
     * <p>Whether anything is left of it is that reading's answer and not this one's: what is here is
     * where to ask.
     */
    record Opened(TermPath at) implements CaseOutcome {}

    /**
     * Naming the case builds it, so there is nothing under it to read.
     *
     * <p>A value, and the plainest one there is. A sum with one of these among its cases has a value
     * whatever the rules do to the others.
     */
    record StandsAlone() implements CaseOutcome {}

    /** The rules leave no value of this case, so nothing under it was owed. */
    record RefusedByTheRules() implements CaseOutcome {}

    /**
     * This reading did not go down the case.
     *
     * <p>How far a walk goes is settled by what was demanded of it and by where a path returns to a
     * declaration already open — neither of which is anything the model says about this case. So
     * what is known about it is nothing, and nothing is not the same answer as
     * {@link RefusedByTheRules}.
     */
    record NotWalked() implements CaseOutcome {}
}
