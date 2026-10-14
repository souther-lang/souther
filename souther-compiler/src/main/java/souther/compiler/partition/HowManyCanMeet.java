package souther.compiler.partition;

import souther.compiler.check.NumericMeasures;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.CountDomain;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.observe.ObservedValue;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Optional;

/**
 * The most elements of a container a count of them meeting a statement comes to, where something
 * says there is a most.
 *
 * <p>Two things say it. The count is of elements the container holds, so it is never more than the
 * most the container holds — which a set or a map has where its element or key has few enough
 * values, and any container has where its rules cap its size. And a set holds each value of its
 * element once, so where its element has only so many values the count is never more than how many
 * of those meet the statement; a set of records of two truths, counted for one of them, holds at
 * most the two records where that one is true.
 *
 * <p>The second is an upper bound read off the values one at a time, at a row holding a set of that
 * value alone, and that is sound only where the statement says the same of a value whatever else
 * the set holds. So it is taken only where three things hold. The container is a set written at a
 * parameter, which is where such a row can be walked. The statement reads nothing but the element,
 * and reads it in forms whose answer is the element's own ({@link #saysOnlyOfTheElement}): one
 * reading how many the set holds, or which of its elements is the last to hold a value, fails at a
 * set of one where a set of more meets it. And the element's values are listed whole, with no
 * number among its parts — a number is listed at values standing for its runs, which are not every
 * value it has ({@link ValuesOfAnElement}). The values are listed under the rules of the place,
 * which may leave values the rules refuse elsewhere; a value too many makes the bound looser and
 * never wrong.
 *
 * <p>A value is counted unless the statement fails of it. One the statement could not be read of
 * may meet it.
 */
final class HowManyCanMeet {

    /** How many values of the element are read before the second bound is given up on. */
    private static final int MOST_VALUES =
            CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.maximum();

    private HowManyCanMeet() {
    }

    /** The most {@code counted} comes to as {@code read} has its container, or none where nothing
     *  says. */
    static Optional<Count> of(CountedElements counted, InputReading read) {
        TermPath container = counted.container();
        Position at = read.domain().at(container);
        if (at == null) {
            return Optional.empty();
        }
        Optional<Count> mostHeld = mostHeld(container, at.type(), read);
        Optional<Count> meeting = ofTheValuesMeeting(counted, at.type(), read);
        if (mostHeld.isPresent() && meeting.isPresent()) {
            return mostHeld.get().compareTo(meeting.get()) <= 0 ? mostHeld : meeting;
        }
        return mostHeld.isPresent() ? mostHeld : meeting;
    }

    /**
     * The most the container at {@code container} holds, or none where nothing says.
     *
     * <p>Read off the number that is how many it holds, as a rule taking {@code Set.size} of it
     * reads it, so what its rules leave that number and what its type leaves it are both in the
     * answer ({@link InputDomain#of}). Not {@link Quantities#mostHeldAt}, which answers where a
     * rule names the size and leaves the type's end out where none does.
     */
    private static Optional<Count> mostHeld(TermPath container, Type type, InputReading read) {
        RuleReadingSource source = read.rules();
        ValueName.Stdlib size = NumericMeasures.takenOf(type, source.inners());
        NumericTerm.TakenOf held = size == null ? null : NumericTerm.TakenOf.asItStands(size,
                container, type, source.inners(), source.symbols());
        if (held == null || !(held.takenAs() instanceof TakenAs.HowManyItHolds)) {
            return Optional.empty();
        }
        NumericDomain.Bounds runs = read.quantities().runsBetween(held);
        int most = runs == null ? Integer.MAX_VALUE : CountDomain.mostFrom(runs.max());
        return most == Integer.MAX_VALUE ? Optional.empty() : Optional.of(Count.of(most));
    }

    /** How many values of the element of a set at a parameter the statement does not fail of, or
     *  none where that is no bound on the count. */
    private static Optional<Count> ofTheValuesMeeting(CountedElements counted, Type type,
                                                      InputReading read) {
        TermPath container = counted.container();
        RuleReadingSource source = read.rules();
        if (!container.steps().isEmpty()
                || !(TypeView.shapeOf(type, source.inners(), source.symbols(), source.kinds(),
                        source.sums()) instanceof Shape.Sequence(Shape.Sequence.Kind kind,
                                Type element))
                || kind != Shape.Sequence.Kind.SET
                || !saysOnlyOfTheElement(counted.meeting(), container.element())) {
            return Optional.empty();
        }
        ValuesOfAnElement.Listed listed = ValuesOfAnElement.of(element, container.element(),
                RuleReadingContext.of(source, read.domain().policy(), read.domain().machines()),
                MOST_VALUES, _ -> null);
        if (listed == null || !listed.all()) {
            return Optional.empty();
        }
        BehaviorInputs where = new BehaviorInputs(List.of(container.head()), List.of(type), source,
                read.domain().policy());
        long meet = 0;
        for (ObservedValue value : listed.values()) {
            AStatementAtARow.HowManyAtARow one = counted.perElement().howManyMeetIn(container,
                    CardinalityComposer.aRowHolding(where, List.of(value)));
            if (one == null) {
                return Optional.empty();
            }
            if (one.meet() + one.unread() > 0) {
                meet++;
            }
        }
        return Optional.of(Count.of(meet));
    }

    /**
     * Whether {@code stated} reads nothing but the element at {@code element}, in forms whose
     * answer at an element is the same whatever else its container holds.
     *
     * <p>A closed list and not a walk over what is read. Which last element holds a value is a
     * question about the others, though it is written at a position of the element; a quantifier
     * and a count read another container, or one inside the element whose answer this does not
     * read; a statement about what a dependency answered, or one nobody read, is not the element's.
     * Each of those is no bound here, and a form added later is none until it is put on this list.
     */
    static boolean saysOnlyOfTheElement(Proposition stated, TermPath element) {
        return switch (stated) {
            case Proposition.Always _ -> true;
            case Proposition.Truth truth -> isOfTheElement(truth.of(), element);
            case Proposition.Present present -> isOfTheElement(present.of(), element);
            case Proposition.InCases cases -> isOfTheElement(cases.of(), element);
            case Proposition.SameValue same -> isOfTheElement(same.one(), element)
                    && isOfTheElement(same.other(), element);
            case Proposition.All all -> all.parts().stream()
                    .allMatch(part -> saysOnlyOfTheElement(part, element));
            case Proposition.Any any -> any.parts().stream()
                    .allMatch(part -> saysOnlyOfTheElement(part, element));
            case Proposition.Compared compared -> switch (compared.relation()) {
                case Relation.Affine affine -> affine.form().coefs().keySet().stream()
                        .allMatch(quantity -> isOfTheElement(quantity, element));
                case Relation.Ordered ordered -> isOfTheElement(ordered.term(), element);
            };
            case Proposition.LastToHold _, Proposition.Some _, Proposition.SomeReachable _,
                 Proposition.OnAnApplication _, Proposition.Unread _, Proposition.Carried _ ->
                    false;
        };
    }

    private static boolean isOfTheElement(DecisionSubject subject, TermPath element) {
        return subject instanceof DecisionSubject.AnInput(TermPath at) && at.isAtOrUnder(element);
    }

    /** A number of the input read at one position under the element; a number taken over a
     *  container, or of how often a value occurs in one, is not. */
    private static boolean isOfTheElement(Quantity quantity, TermPath element) {
        return quantity instanceof DecisionAtom.OfTheInput(NumericTerm.FromOnePosition term)
                && term.position().isAtOrUnder(element);
    }
}
