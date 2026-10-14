package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.PositionId;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.Count;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;

/**
 * The most elements of a container a count of them meeting a statement comes to, where something
 * says there is a most.
 *
 * <p>Two things say it. The count is of elements the container holds, so it is never more than the
 * most the container holds ({@link Quantities#mostHeldAt}) — which a set or a map has where its
 * element or key has few enough values, and any container has where its rules cap its size. And a set holds each value of its
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
 * <p>Listed and walked as the composer lists and walks them ({@link ElementsOfAParameter}), under
 * the same figure. Where the figure stops the listing, the count keeps the most the container
 * holds, and the composer looking for a row between the two stops at the same figure and says so.
 *
 * <p>A value is counted unless the statement fails of it. One the statement could not be read of
 * may meet it.
 */
final class HowManyCanMeet {

    private HowManyCanMeet() {
    }

    /**
     * The most {@code counted} comes to as {@code read} has its container, or none where nothing
     * says.
     *
     * <p>Worked out once for each count a reading reads. The answer is a function of which count
     * it is and of the reading, and a count is cut at every comparison written about it, each of
     * which would otherwise list the element's values and walk a row for each again.
     */
    static Optional<Count> of(CountedElements counted, InputReading read) {
        return read.derived(Known.class, _ -> new Known()).ends
                .computeIfAbsent(counted.identity(), _ -> workedOut(counted, read));
    }

    /** The ends worked out for the counts one reading reads, by which count each is. */
    private static final class Known {
        private final Map<CountedElements.Identity, Optional<Count>> ends =
                new ConcurrentHashMap<>();
    }

    private static Optional<Count> workedOut(CountedElements counted, InputReading read) {
        TermPath container = counted.container();
        Position at = read.domain().at(container);
        if (at == null) {
            return Optional.empty();
        }
        int mostHeld = read.quantities().mostHeldAt(new PositionId(container));
        long held = mostHeld == Integer.MAX_VALUE ? Long.MAX_VALUE : mostHeld;
        long most = Math.min(held, ofTheValuesMeeting(counted, at.type(), read, held));
        return most == Long.MAX_VALUE ? Optional.empty() : Optional.of(Count.of(most));
    }

    /**
     * How many values of the element of a set at a parameter the statement does not fail of, or
     * {@link Long#MAX_VALUE} where that is no bound on the count.
     *
     * <p>The walk stops once as many as {@code held} meet it, past which the count is bounded by
     * the container and not by these.
     */
    private static long ofTheValuesMeeting(CountedElements counted, Type type, InputReading read,
                                           long held) {
        TermPath container = counted.container();
        RuleReadingSource source = read.rules();
        if (!(TypeView.shapeOf(type, source.inners(), source.symbols(), source.kinds(),
                        source.sums()) instanceof Shape.Sequence(Shape.Sequence.Kind kind,
                                Type element))
                || kind != Shape.Sequence.Kind.SET
                || !saysOnlyOfTheElement(counted.meeting(), container.element())) {
            return Long.MAX_VALUE;
        }
        ElementsOfAParameter values = ElementsOfAParameter.of(container, type, element,
                RuleReadingContext.of(source, read.domain().policy(), read.domain().machines()),
                _ -> null);
        if (values == null || !values.listed().all()) {
            return Long.MAX_VALUE;
        }
        long meet = 0;
        for (ObservedValue value : values.listed().values()) {
            if (meet >= held) {
                return held;
            }
            AStatementAtARow.HowManyAtARow one = counted.perElement().howManyMeetIn(container,
                    values.holding(List.of(value)));
            if (one == null) {
                return Long.MAX_VALUE;
            }
            if (one.meet() + one.unread() > 0) {
                meet++;
            }
        }
        return meet;
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
