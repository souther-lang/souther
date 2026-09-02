package souther.compiler.inputs;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
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

    /** The same region, with these positions standing at these values. */
    SearchRegion given(Map<NumericTerm, Count> fixed);

    /** The same, of one position. */
    default SearchRegion given(NumericTerm term, Count fixed) {
        return given(Map.of(term, fixed));
    }

    /** Where the values of {@code form} run inside this region, or null at either end where
     *  nothing bounds them. */
    NumericDomain.Bounds runsBetween(LinearForm<NumericTerm> form);

    /** The same, of one term — the one-term case of the question above and not a second answer to
     *  it. */
    default NumericDomain.Bounds runsBetween(NumericTerm term) {
        return runsBetween(LinearForm.atom(term));
    }

    /**
     * Why nothing is left here, or empty where nothing proved it.
     *
     * <p>Empty is not "there is a value", the same as everywhere else. A search reading it that way
     * would take the absence of a proof for one.
     */
    Optional<EmptyInput> emptiness();
}
