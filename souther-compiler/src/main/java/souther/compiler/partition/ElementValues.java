package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.function.BiFunction;

/**
 * The values an element of a container is listed at, and the two ways each is read: as part of a
 * row holding the container, and as the element alone.
 *
 * <p>Two readers list them: the composer choosing which values a container is made of
 * ({@link CardinalityComposer}), and the most a count of the elements comes to
 * ({@link HowManyCanMeet}). Both list them here under one figure, so a value one of them reads is
 * a value the other reads, and the figure says one thing about both.
 *
 * <p>The two ways of reading are two questions. A row holding the container holds those values
 * and no others, which is what a composed row is. The element alone holds one value and says
 * nothing of anything else — not of the other elements, not of the container, not of any other
 * position — so a statement read at it is told it could not walk anywhere but into the element,
 * and that reads as not being able to tell and never as failing. What a statement fails of there,
 * it fails of wherever the value stands.
 */
final class ElementValues {

    /** How many values of the element are listed before the listing stops. */
    private static final int MOST_VALUES =
            CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.maximum();

    /** The name the element alone is read under, as the one value a row of it holds. */
    private static final String ALONE = "element";

    private final TermPath container;
    private final Type element;
    private final RuleReadingContext reading;
    private final ValuesOfAnElement.Listed listed;

    private ElementValues(TermPath container, Type element, RuleReadingContext reading,
                          ValuesOfAnElement.Listed listed) {
        this.container = container;
        this.element = element;
        this.reading = reading;
        this.listed = listed;
    }

    /**
     * The values of {@code element}, the element of the container at {@code container}, as
     * {@link ValuesOfAnElement#of} lists them — or null where some part of the element is one
     * nothing here lists values of.
     *
     * @param numbersAt the values a number standing at a position, of the type read there, is
     *                  read at, or null where none are chosen there
     */
    static ElementValues of(TermPath container, Type element, RuleReadingContext reading,
                            BiFunction<TermPath, TypeView, List<ObservedValue>> numbersAt) {
        ValuesOfAnElement.Listed listed = ValuesOfAnElement.of(element, container.element(),
                reading, MOST_VALUES, numbersAt);
        return listed == null ? null : new ElementValues(container, element, reading, listed);
    }

    /** How many values of one part of the element a caller may hand {@code numbersAt}: no more
     *  than are listed of the whole. */
    static int mostOfAPart() {
        return MOST_VALUES;
    }

    /** The values listed, and whether the figure stopped the listing. */
    ValuesOfAnElement.Listed listed() {
        return listed;
    }

    /**
     * A row holding {@code values} as the container, and nothing else.
     *
     * <p>A container that is a parameter is the row's one parameter. One inside a parameter is
     * read as a row of its own, as the element alone is: a path inside it is read in it, and every
     * other could not be walked, which is what the row holding a parameter answers of the
     * parameters beside it.
     *
     * @param type the container's type
     */
    BorderQuantity.Observation holding(Type type, List<ObservedValue> values) {
        return holding(container, reading, type, values);
    }

    /**
     * {@link #holding(Type, List)} of the container at {@code container}, which needs no listing
     * of the values of an element: a container of none is one whether or not an element can be.
     */
    static BorderQuantity.Observation holding(TermPath container, RuleReadingContext reading,
                                              Type type, List<ObservedValue> values) {
        boolean aParameter = container.steps().isEmpty();
        BorderQuantity.Observation row = new StandingAtAPoint.DiscoveringRow(
                new StandingAtAPoint.RowWalk(new BehaviorInputs(
                        List.of(aParameter ? container.head() : ALONE), List.of(type),
                        reading.source(), reading.policy()),
                        new ObservedInputs(List.of(new ObservedValue.Sequence(values)),
                                new Generator.Watched.NotRun(),
                                new AnswerObservation.NotAnswered())));
        return aParameter ? row : new Alone(container, row);
    }

    /**
     * {@code holding}, a row holding the container, read as the one element of the container at
     * {@code outer} holding it: what is read of every element of that container is read of this
     * one, and of the container inside it, which is all of them there are.
     *
     * <p>For the elements of the containers inside the elements of {@code outer}, every one of them
     * put end to end, chosen as one container of them: so many elements in one container, read
     * across all of them, are what they are across any containers they are shared out over.
     */
    static BorderQuantity.Observation asTheOneElementOf(TermPath outer,
                                                        BorderQuantity.Observation holding) {
        return new TheOneElementOf(outer, holding);
    }

    /** {@link #asTheOneElementOf}. */
    private record TheOneElementOf(TermPath outer, BorderQuantity.Observation within)
            implements BorderQuantity.Observation {

        @Override
        public WalkResult<ObservationAtPoint> at(TermPath path) {
            return within.at(path);
        }

        @Override
        public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
            return within.everyValueAt(path);
        }

        /** This one, as the one element of the outer container; the rest as the row holds, each
         *  read the same way. */
        @Override
        public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath of) {
            if (of.equals(outer)) {
                return WalkResult.reached(List.of(this));
            }
            return switch (within.eachElementOf(of)) {
                case WalkResult.CouldNotWalk<List<BorderQuantity.Observation>> _ ->
                        WalkResult.couldNotWalk();
                case WalkResult.Reached(List<BorderQuantity.Observation> each) -> {
                    List<BorderQuantity.Observation> out = new ArrayList<>();
                    each.forEach(one -> out.add(new TheOneElementOf(outer, one)));
                    yield WalkResult.reached(out);
                }
            };
        }
    }

    /** The element alone, holding {@code value}. */
    BorderQuantity.Observation alone(ObservedValue value) {
        return new Alone(container.element(), new StandingAtAPoint.DiscoveringRow(
                new StandingAtAPoint.RowWalk(
                        new BehaviorInputs(List.of(ALONE), List.of(element), reading.source(),
                                reading.policy()),
                        new ObservedInputs(List.of(value), new Generator.Watched.NotRun(),
                                new AnswerObservation.NotAnswered()))));
    }

    /**
     * A reading of one part of the input, walked from that part: a path under it is read in it,
     * and every other path could not be walked.
     *
     * @param part   where the part stands in the input
     * @param within the part read as a row of its own, under {@link #ALONE}
     */
    private record Alone(TermPath part, BorderQuantity.Observation within)
            implements BorderQuantity.Observation {

        @Override
        public WalkResult<ObservationAtPoint> at(TermPath path) {
            TermPath inside = inside(path);
            return inside == null ? WalkResult.couldNotWalk() : within.at(inside);
        }

        @Override
        public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
            TermPath inside = inside(path);
            return inside == null ? WalkResult.couldNotWalk() : within.everyValueAt(inside);
        }

        /** The elements of a container inside the part, each read the same way. */
        @Override
        public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath of) {
            TermPath inside = inside(of);
            if (inside == null) {
                return WalkResult.couldNotWalk();
            }
            return switch (within.eachElementOf(inside)) {
                case WalkResult.CouldNotWalk<List<BorderQuantity.Observation>> _ ->
                        WalkResult.couldNotWalk();
                case WalkResult.Reached(List<BorderQuantity.Observation> each) -> {
                    List<BorderQuantity.Observation> out = new ArrayList<>();
                    each.forEach(one -> out.add(new Alone(part, one)));
                    yield WalkResult.reached(out);
                }
            };
        }

        /** {@code path} as the part's own row names it, or null where it is not inside the
         *  part. */
        private TermPath inside(TermPath path) {
            return path.isAtOrUnder(part) ? new TermPath(ALONE,
                    path.steps().subList(part.steps().size(), path.steps().size())) : null;
        }
    }
}
