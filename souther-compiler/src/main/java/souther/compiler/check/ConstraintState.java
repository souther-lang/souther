package souther.compiler.check;

import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;
import souther.compiler.values.AdmissibleValues;

import java.util.Map;

/**
 * What the rules say, in each of the languages this reading has for saying it.
 *
 * <p>Several domains and one state. A clause relates numbers, or settles a predicate that relates to
 * nothing, and each of those is written where something can be reasoned about it — but what a caller
 * asks of them together is one question, and it is whether anything at all satisfies what has been
 * taken in. That is {@link #isBottom}, and it is asked of the whole because a reader that asked one
 * domain would answer that a value exists whenever the domain it happened to ask had nothing to say.
 * {@code value == "A"} beside {@code value /= "A"} reaches no number and leaves the predicates
 * contradictory, and a count taken from the numbers alone called that type inhabited.
 *
 * <p>The parts are readable, and only in one direction. A reader wanting the numbers may have them —
 * an interval is what a bound is read off, and nothing else answers that — but a reader asking
 * whether a value exists asks here and never assembles the answer out of the parts. A domain added
 * later is a component of this and an arm of {@link #isBottom}, and every such reader has it without
 * being touched.
 *
 * <p>One reader still asks the numbers alone, and it is the other question. Whether a path is
 * reached — whether the conditions guarding a construction can all hold — is asked of
 * {@code numbers} where the walk reads a branch, so a path made impossible by predicates alone is
 * walked and what stands on it is reported. That is a mistake of the same shape as the one above,
 * and it is not this one: what it moves is which constructions are reported at, and a change to
 * that is its own change with its own reason to make.
 */
record ConstraintState(NumericDomain<Term> numbers, PredicateFacts facts,
                       AdmissibleValues<Term> values) {

    /** Nothing taken in, so nothing ruled out. */
    static ConstraintState top() {
        return new ConstraintState(NumericDomain.top(), PredicateFacts.none(),
                AdmissibleValues.top());
    }

    /**
     * Whether nothing satisfies what has been taken in.
     *
     * <p>Every domain, because each of them can hold the whole state's contradiction on its own: what
     * one of them cannot express it leaves alone, so a contradiction found anywhere is a
     * contradiction, and one found nowhere is only what these readings were able to show.
     */
    boolean isBottom() {
        return numbers.isBottom() || facts.isBottom() || values.isBottom();
    }

    /** This, with {@code f rel 0} taken as holding. */
    ConstraintState taking(LinearForm<Term> f, Rel rel, Map<Term, Granularity> kinds) {
        return new ConstraintState(numbers.assume(f, rel, kinds), facts, values);
    }

    /** This, with the predicate {@code key} taken as holding, or as failing. */
    ConstraintState taking(Term key, boolean positive) {
        return new ConstraintState(numbers, facts.assume(key, positive), values);
    }

    /** This, with {@code admitted} taken as holding of the positions it speaks about. */
    ConstraintState taking(AdmissibleValues<Term> admitted) {
        return new ConstraintState(numbers, facts, values.meet(admitted));
    }
}
