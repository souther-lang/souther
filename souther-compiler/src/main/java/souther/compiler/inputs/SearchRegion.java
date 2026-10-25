package souther.compiler.inputs;

import souther.compiler.check.HeldClass;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.OrderedRuns;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.numeric.Rel;
import souther.compiler.values.ValueSet;

import java.util.Collection;
import java.util.List;
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

    /**
     * The class the value at {@code place} is held to besides where it runs: what its declarations
     * hold it to, met with the remainders this region fixed beside it.
     *
     * <p>{@link #projectionOf} says where the value runs and not which numbers of the run it may be:
     * a search that chooses it is held to this as well. A region that reads no declarations and
     * fixes no remainder says nothing of one, which is what the default is.
     */
    default HeldClass classAt(NumericTerm.ValueOf place) {
        return HeldClass.NONE;
    }

    /**
     * The runs a choice of ranges in its declarations left the value at {@code place}, lowest
     * first, or null where they leave it one ({@link Position#runsApart}).
     *
     * <p>{@link #projectionOf} is the ends around them, and a search choosing the value inside
     * those ends is held to these as well: a value in a gap between two of them is one every
     * alternative refuses. A region that reads no declarations says nothing of them, which is what
     * the default is.
     */
    default OrderedRuns runsAt(NumericTerm.ValueOf place) {
        return null;
    }

    /**
     * The values the declarations of the position {@code term} is read of admit it, as far as they
     * were read.
     *
     * <p>Beside {@link #classAt} and for the same reason: a range says where a value runs and
     * not which values of the run the position may hold, and a position held to {@code "a"} or
     * {@code "b"} holds none of the strings between them. Read and not proved: what the rules that
     * were read admit, so a value outside it is refused and a value inside it is not shown to be one
     * a row can hold. A region that reads no position says nothing of one, which is what the default
     * is.
     *
     * <p>Values of the position whatever {@code term} takes of it: the strings of a string, and not
     * its lengths. What those come to as the number {@code term} is, is {@link #heldAt}.
     */
    default ValueSet admittedAt(NumericTerm.FromOnePosition term) {
        return ValueSet.ANY;
    }

    /**
     * The values the declarations hold the number {@code term} to, on the order it is answered on.
     *
     * <p>The position's own values where {@code term} is its value, and the numbers they come to
     * where {@code term} is a number taken of it: a string held to {@code "a"} or {@code "bbb"} is
     * held to a length of one or three. The one answer every reader of such a number takes — a
     * border refusing a point, a class standing for a run, a search walking the numbers — so that
     * none of them puts the strings to the lengths, which admits no length at all, or reads the
     * strings through the term again on its own.
     *
     * <p>Only ever as wide as {@link #admittedAt}: every value where the numbers were not worked
     * out.
     */
    default ValueSet heldAt(NumericTerm.FromOnePosition term) {
        return ValueSet.ANY;
    }

    /**
     * Every value the declarations admit the position {@code terms} are taken of, each with what
     * every one of them reads of it — or null where that is not worked out.
     *
     * <p>What a reader asking several numbers of one position together asks, and never the sets
     * {@link #heldAt} answers for each of them met with one another. Which value comes to which
     * numbers is what those sets leave out, so a combination each set holds a number of may be one
     * no value comes to.
     *
     * <p>Null where the terms are not all of one position, where the position admits no finite set
     * of values, or where a value of it is read as no number of one of the terms: a reader then
     * knows nothing of the values together, as a region that reads no position does not, which is
     * what the default is.
     */
    default ReadingsOfEachValue readingsOfEach(List<NumericTerm.FromOnePosition> terms) {
        return null;
    }

    /** The same, of one term — the one-term case of the question above and not a second answer to
     *  it. */
    default NumericDomain.FormProjection projectionOf(NumericTerm term) {
        return projectionOf(LinearForm.atom(term));
    }

    /**
     * Where {@code term} runs when the terms in {@code alongside} are still to be chosen.
     *
     * <p>What each of them is on its own is put on the rules before {@code term} is read off them,
     * so a relation between the two bounds {@code term} by the ends the other has from its type. The
     * answer holds every assignment of all of them this region admits, and is narrower than
     * {@link #projectionOf(NumericTerm)} only by what such a relation takes out. Terms that no row
     * has together, or with {@code term}, add nothing: the answer is then that of {@code term} on
     * its own, whatever order they are in. A region that reads no relations has nothing to add,
     * which is what the default is.
     */
    default NumericDomain.FormProjection projectionOf(NumericTerm term,
                                                      Collection<? extends NumericTerm> alongside) {
        return projectionOf(term);
    }

    /**
     * A run of {@code term} every value of which some row in this region takes, at the term's own
     * spacing — or null where that is not shown.
     *
     * <p>Not {@link #projectionOf}, which is where the values lie: a run can be known without being
     * filled, its ends can be rounded past the rules', and a value can be taken out of it
     * ({@link #apartAt}) or the values held to a class ({@link #classAt}).
     * This is shown of all of that at once and answered as the run itself, so a reader is never
     * left to put a range from one answer together with a proof from another.
     *
     * <p>Null where nothing showed it, which is not that the run has gaps — and so for a region
     * that has no proof to give, which is what the default is.
     */
    default NumericDomain.Bounds wholeRunOf(NumericTerm.FromOnePosition term) {
        return null;
    }

    /**
     * Why nothing is left here, or empty where nothing proved it.
     *
     * <p>Empty is not "there is a value", the same as everywhere else. A search reading it that way
     * would take the absence of a proof for one.
     */
    Optional<EmptyInput> emptiness();
}
