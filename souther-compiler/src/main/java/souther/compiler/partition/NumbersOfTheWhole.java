package souther.compiler.partition;

import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.semantics.TakenAs;

/**
 * The numbers of a container taken as a whole: what its elements come to at one place, and how
 * many it holds.
 *
 * <p>Asked of the term in one place, because three readers turn on the same answer. Where a row
 * writes a number inside an element is beside the container it is a number of; whether one value
 * answers them together is a way of composing that container; and the composing fixes these numbers
 * before it chooses an element. Read three times, a total one of them knew and another did not
 * would be written as two places again.
 */
final class NumbersOfTheWhole {

    /**
     * What each element adds to a total: {@code weight} times the number at {@code place} inside
     * it, and {@code constant}.
     *
     * @param place  where inside each element the number added stands
     * @param weight what the number is multiplied by, never nought
     */
    record AddedUp(TermPath place, ExactRatio weight, ExactRatio constant) {}

    /**
     * What each element adds to {@code term}, where it is a total of one place of each element of
     * one container, or of a form of that place — or null where it is no such total.
     */
    static AddedUp addedUp(NumericTerm term) {
        return switch (term) {
            case NumericTerm.TakenOver over
                    when over.takenAs() instanceof TakenAs.TheSumOfWhatItHolds
                            && over.source() instanceof RunSource.ProjectedOccurrences run ->
                    new AddedUp(run.subjectPath(), ExactRatio.ONE, ExactRatio.ZERO);
            case NumericTerm.TakenOver over
                    when over.takenAs() instanceof TakenAs.TheSumOfWhatItHolds
                            && over.source() instanceof RunSource.ComputedOccurrences run
                            && run.computation() instanceof ElementValue.Affine affine
                            && affine.form().coefs().size() == 1 -> {
                var each = affine.form().coefs().entrySet().iterator().next();
                yield each.getValue().isZero() ? null : new AddedUp(
                        each.getKey().from(run.elements()), each.getValue(),
                        affine.form().constant());
            }
            case NumericTerm.TakenOf taken
                    when taken.takenAs() instanceof TakenAs.TheSumOfWhatItHolds
                            && !taken.position().insideAContainer() ->
                    new AddedUp(taken.position().element(), ExactRatio.ONE, ExactRatio.ZERO);
            case NumericTerm.FromOnePosition _, NumericTerm.TakenOver _,
                 NumericTerm.Multiplicity _, NumericTerm.OccurrencesOfItsValue _,
                 NumericTerm.OccurrencesOfAKey _, NumericTerm.ExtremeOfItsKey _,
                 NumericTerm.GatheredUnderItsKey _, NumericTerm.GatheredUnderAKey _,
                 NumericTerm.ProductOf _ -> null;
        };
    }

    /** Whether {@code term} is how many the container at {@code container} holds. */
    static boolean howManyItHolds(NumericTerm term, TermPath container) {
        return term instanceof NumericTerm.TakenOf taken
                && taken.takenAs() instanceof TakenAs.HowManyItHolds
                && taken.position().equals(container);
    }

    /**
     * The container {@code term} is a number of as a whole — what its elements come to at one
     * place, or how many it holds — or null where it is neither.
     */
    static TermPath containerOf(NumericTerm term) {
        AddedUp added = addedUp(term);
        if (added != null) {
            return added.place().containersHoldingIt().getLast();
        }
        return term instanceof NumericTerm.TakenOf taken
                && taken.takenAs() instanceof TakenAs.HowManyItHolds
                && !taken.position().insideAContainer() ? taken.position() : null;
    }

    /**
     * Whether {@code term} is one number of a row and no number of an element: an input standing
     * outside every container, or a number of a container as a whole that stands outside every
     * container.
     *
     * <p>Asked of where the number stands and not of the path it reads. What a container's
     * elements come to reads a place inside the container and is one number however many elements
     * it holds; a reader asking whether that place is inside a container takes the total of another
     * container for a number of some element of it, and leaves a statement reading one with nothing
     * standing beside its elements.
     */
    static boolean oneNumberOfTheRow(NumericTerm term) {
        TermPath whole = containerOf(term);
        return !(whole != null ? whole : term.subjectPath()).insideAContainer();
    }

    /** Whether {@code term} is a number of the container at {@code container} as a whole. */
    static boolean ofTheWhole(NumericTerm term, TermPath container) {
        return container.equals(containerOf(term));
    }

    /**
     * Whether {@code term} is a number of some container written at {@code at} as a whole: the
     * value at {@code at}, or one inside it. A row composing that value fixes such a number with
     * the container's elements, so it is no number standing beside them.
     */
    static boolean ofAWholeWrittenAt(NumericTerm term, TermPath at) {
        TermPath whole = containerOf(term);
        return whole != null && whole.isAtOrUnder(at);
    }

    /**
     * Whether {@code term} stands beside every element of the container at {@code container}
     * alike: one number of the row ({@link #oneNumberOfTheRow}) that is no number of that
     * container as a whole, which is what the elements chosen make it ({@link ContainerAsAWhole}).
     *
     * <p>The one answer to which numbers a statement of the elements reads are placed before the
     * elements are chosen, so the search placing them and every reader taking what it placed
     * agree on it.
     */
    static boolean standsBeside(NumericTerm term, TermPath container) {
        return oneNumberOfTheRow(term) && !ofTheWhole(term, container);
    }

    private NumbersOfTheWhole() {}
}
