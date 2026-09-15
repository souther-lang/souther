package souther.compiler.inputs;

import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;

import java.util.Map;
import java.util.Optional;

/**
 * Where a row for one coverage item has to be written.
 *
 * <p><b>Not a {@link Quantities}, on purpose.</b> What the declarations leave an input is what says
 * which borders the rows are owed at; where a row for one of those borders is looked for is
 * narrower, because a rule a row has to pass before it reaches the border narrows the search and
 * settles nothing about whether the border exists. Those are two questions, and a type that
 * answered both would let the second's answer reach the first's readers — where it would take
 * obligations away as this compiler learned more, which is the one direction a coverage measure may
 * not move in.
 *
 * <p>So the two are apart and neither is the other's subtype. What they share is the algebra
 * underneath, which is where sharing costs nothing: a renaming, a meeting and a projection are the
 * same acts whoever is asking. A subtype would put one of these back where the other is expected,
 * and the boundary would be a thing to remember rather than a thing that holds.
 *
 * <p><b>Never wider than the declarations, and never narrower than what arrives.</b> Refining is
 * narrowing and only that ({@code R.assuming(c)} is inside {@code R}), and a condition this cannot
 * read narrows nothing rather than being approximated — so
 *
 * <pre>what reaches the border ⊆ this ⊆ what the declarations leave</pre>
 *
 * holds however much of a body was read. The left inclusion is what lets a walk of the whole of this
 * that reaches nothing prove the item is out of reach; the right is why a search that gives up
 * proves nothing. Neither survives a reading that narrowed on a condition it had not established.
 *
 * <p>Which also says what this is not: it is not the set of rows that reach the border. A condition
 * of a shape the arithmetic has no word for narrows nothing, so this may hold rows that never
 * arrive and a row found here is a row to try and not a row shown to arrive — what shows that is
 * running it. Only the inclusion is promised, never that it is strict: a condition nothing took in
 * may be implied by the ones that were.
 */
public interface SearchRegion {

    /**
     * The same region, with {@code form rel 0} taken in.
     *
     * <p>A refinement of where a row may be written and not a new reading of anything. Taking in
     * accumulates, so the order the conditions on the way to a border arrived in does not reach the
     * answer, and taking one in twice is taking it in once.
     *
     * <p>Where the arithmetic has nothing to say about a condition — a form over a position whose
     * values it cannot count, a subject it has no spacing for — what comes back is this region
     * unchanged. Which is the direction that keeps the inclusions above: a condition nothing took in
     * leaves a region that still holds every row that arrives, and a region narrowed on a condition
     * nothing established would leave it narrower than they are.
     */
    SearchRegion assuming(LinearForm<NumericTerm> form, Rel rel);

    /**
     * The same region, with {@code term rel at} taken in on the order {@code term} stands on.
     *
     * <p>The other value vocabulary, for a position whose values do not count to numbers. A string
     * is ordered and stands no measurable distance from another, so a rule holding one against a
     * written value states where on the order it lies and states no arithmetic — and the form above
     * has nowhere to put a place that is not a number.
     *
     * <p>One position and a place, never a form: a sum needs its terms to add, and two strings do
     * not. A relation between two such positions is a distance and goes to the form above, which is
     * why this is asked only where a written value is one side of the comparison.
     *
     * <p>{@code rel} says where a run stops. A relation that leaves a hole rather than an end is
     * not one this narrows by, and it is refused where such a constraint would be built rather than
     * arriving here to be dropped — a caller whose condition went nowhere would otherwise have no
     * way of finding out.
     *
     * <p>Unchanged where nothing here orders that term, on the same principle as the form above: a
     * condition nothing took in leaves a region that still holds every row that arrives.
     */
    SearchRegion assuming(NumericTerm.FromOnePosition term, Place at, Rel rel);

    /**
     * The same region, with {@code term} held away from {@code at}.
     *
     * <p>A hole, which is what a disequality states and is not an end: the values either side of it
     * are both still there. A range cannot say it, so it is its own verb rather than a relation the
     * one above would have to refuse.
     *
     * <p>What it changes is {@link #emptiness}: a row standing where a rule holds the position away
     * is a row that cannot be written. There is no question here for a chooser to ask before it
     * offers a value, because nothing yet could spend one — on an order that counts nothing the
     * places a chooser can name are the ones a rule wrote, so a hole at one of them leaves it with
     * nothing else to offer and the refusal is what says so.
     */
    SearchRegion apartFrom(NumericTerm.FromOnePosition term, Place at);

    /**
     * The same region, with these positions standing at these values.
     *
     * <p>A place and not a number, because what a position stands at is a place on its carrier's
     * order. A count is one kind of place; a string is the other, and a row writes one there as
     * surely as it writes a number anywhere else. Taken as a number, every value a carrier that
     * counts nothing offers had to be dropped by whoever was choosing one — which is a position
     * nothing could compose a value for, said of a position whose values were in hand.
     *
     * <p>What the declarations are told of it is theirs to decide. The rules are read with the
     * arithmetic, so a fixing they have no number for narrows this region and is not among what
     * they are asked to solve.
     */
    SearchRegion given(Map<NumericTerm, Place> fixed);

    /** The same, of one position. */
    default SearchRegion given(NumericTerm term, Place fixed) {
        return given(Map.of(term, fixed));
    }

    /**
     * Where the values of {@code form} run inside this region, or that this region leaves it
     * nowhere to run.
     *
     * <p><b>Not a range, because one of the answers is not one.</b> A region shown to hold nothing
     * has no assignment to project, and a range with neither end says the form is at every value —
     * the widest answer there is, handed back by the narrowest region there is. A search reading it
     * spends what it is allowed on values the rules already refuse and reports what it came to as a
     * figure of this compiler's, which is the reading ADR-0091 is written against.
     *
     * <p>Within a region that holds something, a {@code null} end is one nothing bounds.
     */
    NumericDomain.FormProjection projectionOf(LinearForm<NumericTerm> form);

    /** The same, of one term — the one-term case of the question above and not a second answer to
     *  it. */
    default NumericDomain.FormProjection projectionOf(NumericTerm term) {
        return projectionOf(LinearForm.atom(term));
    }

    /**
     * Why nothing is left here, or empty where nothing proved it.
     *
     * <p>Empty is not "there is a value", the same as everywhere else. A search reading it that way
     * would take the absence of a proof for one.
     */
    Optional<EmptyInput> emptiness();
}
