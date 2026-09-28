package souther.compiler.inputs;

import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
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
     * This region asked to take {@code form rel 0} in, and whether it could.
     *
     * <p>A refinement of where a row may be written and not a new reading of anything. Taking in
     * accumulates, so the order the conditions on the way to a border arrived in does not reach the
     * answer, and taking one in twice is taking it in once.
     *
     * <p><b>Whether it was taken in is the answer and not what became of the region.</b> A
     * constraint already taken in is taken in again and leaves the region where it was, and a
     * constraint this algebra has no way to carry leaves it there too — one of those is a region
     * that represents the condition and the other is a region that does not, and a caller reading
     * the two off the region it got back reads them as one. Which is what left a search composing
     * against rules wider than the rows that reach it while every account of the way said the
     * search had been narrowed.
     *
     * <p>A refusal is not an error and the region it leaves is still sound: what comes back
     * unnarrowed still holds every row that arrives, which is the direction the inclusions above
     * need. What a caller owes is to say so — by declining the condition rather than recording it
     * as one the search was narrowed by, or by giving up on what it was composing.
     */
    Assumption assuming(LinearForm<NumericTerm> form, Rel rel);

    /**
     * What asking a region to take a constraint in came to.
     *
     * <p>Two answers and not a region, for the reason
     * {@link SearchRegion#assuming(LinearForm, Rel)} gives: a region that took
     * the constraint in and one that has no way to carry it are told apart by nothing a reader can
     * see in the region itself.
     */
    sealed interface Assumption {

        /** The region with the constraint taken in, which is a region that represents it. Not
         *  necessarily a different region: a constraint already taken in leaves it where it was,
         *  and that is a region that represents it as surely as the first taking did. */
        record Taken(SearchRegion region) implements Assumption {}

        /** The constraint is one this region's algebra cannot carry, so the region is unchanged
         *  and does not represent it. */
        record Refused(Refusal why) implements Assumption {}

        /**
         * The region that took it in, where it did.
         *
         * <p>For a caller that has already established the constraint is representable — one
         * narrowing a region by what an account says was taken in, where a refusal is this
         * compiler's two readings of one constraint disagreeing. Everybody else answers the
         * refusal, since what comes back from one is a region that says less than the caller
         * needs.
         */
        default SearchRegion taken() {
            return switch (this) {
                case Taken(SearchRegion region) -> region;
                case Refused(Refusal why) -> throw new IllegalStateException(
                        "a constraint this region was to have taken in was refused by it: " + why);
            };
        }
    }

    /** Why a region cannot carry a constraint it was asked to take in. */
    sealed interface Refusal {

        /**
         * One of the form's terms stands on no order this region measures values on.
         *
         * <p>Which is not the same as an order that counts nothing: a string is ordered and two
         * strings stand a distance apart, and a form over them is carried here. This is a position
         * with no order at all — a record compared with another is a difference between two of them
         * that is a distance on nothing.
         */
        record NoOrderUnderATerm(NumericTerm term) implements Refusal {}
    }

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
     * <p>What it changes is {@link #emptiness}, and what it is read back through is {@link #apartAt}.
     * Both are needed and they are not one answer: the first refuses a row already written at the
     * place, and the second is what a chooser narrows by so that it never writes one there. Left to
     * the first alone, a position whose order has no step is offered the one place a run gives up and
     * has nothing to offer once that place is the hole.
     */
    SearchRegion apartFrom(NumericTerm.FromOnePosition term, Place at);

    /**
     * Which places this holds {@code term} away from.
     *
     * <p>What a chooser asks before it offers a value. A run says where a position stops and has no
     * word for a value taken out of the middle of it, so a chooser reading the run alone offers a
     * place this refuses and finds out afterwards — which costs it nothing wherever the order steps
     * and costs it every candidate it had where the order does not.
     *
     * <p>Asked of the region rather than kept by whoever narrowed it. A caller that remembered the
     * holes it put in would be holding a second copy of what this answers, and the two would be one
     * region for the emptiness and another for the search.
     *
     * <p>Empty where nothing holds the position away, which is every position of every region until
     * a disequality is taken in. Never null.
     */
    PlacesApart apartAt(NumericTerm.FromOnePosition term);

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
