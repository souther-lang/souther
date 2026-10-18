package souther.compiler.partition;

import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Proposition;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Whether a run made a comparison on the elements a reading of a row names
 * ({@link ElementsMetOn}), put to the readings of rows.
 *
 * <p>Three answers, as a statement put to a row has: made there, not made there, or not known —
 * and the third says why. What stops an operation on an element is read off the row the way any
 * statement about its elements is ({@link AStatementAtARow}); a part of it nothing read, or one no
 * value of the row settles, leaves the answer unknown rather than either of the other two.
 *
 * <p>What the elements of one occurrence of a container came to is worked out once, however many
 * readings ask about one of its elements: the readings of a row are one per element, and each asking
 * after every element before it would read the container once per element.
 */
final class MetOnARow {

    /** What is known of each container, the outermost first, as what is put to a row. */
    private final List<Level> levels;

    /** What a row meets for the comparison to be made through it at all, put to rows; null where
     *  nothing is asked. */
    private final AStatementAtARow made;

    private MetOnARow(List<Level> levels, AStatementAtARow made) {
        this.levels = levels;
        this.made = made;
    }

    /** {@code metOn}, ready to be put to the readings of a behavior's rows. */
    static MetOnARow of(ElementsMetOn metOn, String behavior, Quantities quantities) {
        List<Level> levels = new ArrayList<>();
        for (ElementsMetOn.Level each : metOn.levels()) {
            levels.add(switch (each) {
                case ElementsMetOn.Level.StopsAt(TermPath container, Proposition stops) ->
                        new Stopping(container, AStatementAtARow.of(stops, behavior, quantities));
                case ElementsMetOn.Level.NotSaidOf(TermPath container, ReadingGap why) ->
                        new NotSaidOf(container, why);
                case ElementsMetOn.Level.NotSaidAnywhere(ReadingGap why) ->
                        new NotSaidAnywhere(why);
            });
        }
        return new MetOnARow(List.copyOf(levels),
                metOn.made() instanceof Proposition.Always(boolean always) && always ? null
                        : AStatementAtARow.of(metOn.made(), behavior, quantities));
    }

    /**
     * Whether a run that got as far as the comparison made it on the elements {@code reading}
     * names.
     *
     * <p>Not made in some container settles it, whatever else is not known: a run that stopped
     * before the element in one container never got to the closure inside it.
     */
    AStatementAtARow.Answer at(BorderQuantity.Observation reading) {
        // What every comparison inside no such closure comes to, asked of every reading standing
        // at one of its points.
        if (made == null && levels.isEmpty()) {
            return AStatementAtARow.Answer.HOLDS;
        }
        Set<ReadingGap> unknown = new LinkedHashSet<>();
        if (made != null) {
            switch (made.at(reading)) {
                case AStatementAtARow.Answer.Fails _ -> {
                    return AStatementAtARow.Answer.FAILS;
                }
                case AStatementAtARow.Answer.CouldNotTell(var why) -> unknown.addAll(why);
                case AStatementAtARow.Answer.Holds _ -> { }
            }
        }
        for (Level level : levels) {
            switch (level.at(reading)) {
                case AStatementAtARow.Answer.Fails _ -> {
                    return AStatementAtARow.Answer.FAILS;
                }
                case AStatementAtARow.Answer.CouldNotTell(var why) -> unknown.addAll(why);
                case AStatementAtARow.Answer.Holds _ -> { }
            }
        }
        return unknown.isEmpty() ? AStatementAtARow.Answer.HOLDS
                : new AStatementAtARow.Answer.CouldNotTell(unknown);
    }

    /** What is known of one container, put to a reading of a row. */
    private sealed interface Level permits Stopping, NotSaidOf, NotSaidAnywhere {

        /** Whether the comparison was made on what {@code reading} chose of the container. */
        AStatementAtARow.Answer at(BorderQuantity.Observation reading);
    }

    /**
     * Not said of the elements of {@code container}: a reading that chose one of them is not known
     * to have been met through it, and one that chose none is about none of them.
     */
    private record NotSaidOf(TermPath container, ReadingGap why) implements Level {

        @Override
        public AStatementAtARow.Answer at(BorderQuantity.Observation reading) {
            return switch (reading.among(container)) {
                case WalkResult.CouldNotWalk<BorderQuantity.Among> _ ->
                        new AStatementAtARow.Answer.CouldNotTell(Set.of(ReadingGap.COULD_NOT_WALK));
                case WalkResult.Reached(BorderQuantity.Among among) -> among.chosen() == null
                        ? AStatementAtARow.Answer.HOLDS
                        : new AStatementAtARow.Answer.CouldNotTell(Set.of(why));
            };
        }
    }

    /** Not said of the elements of whichever container a reading chose an element of. */
    private record NotSaidAnywhere(ReadingGap why) implements Level {

        @Override
        public AStatementAtARow.Answer at(BorderQuantity.Observation reading) {
            return reading.choseAnElement()
                    ? new AStatementAtARow.Answer.CouldNotTell(Set.of(why))
                    : AStatementAtARow.Answer.HOLDS;
        }
    }

    /**
     * One container stopped short in.
     *
     * <p>What one occurrence of it came to is the same for every reading of it, so it is read
     * once for all of them ({@link #readAt}), and kept by the walk over the row rather than here:
     * this lives as long as the line, and the rows it is asked of do not.
     */
    private static final class Stopping implements Level, BorderQuantity.ReadAlike<Prefix> {

        private final TermPath container;

        /** What stops the operation, put to rows. */
        private final AStatementAtARow stops;

        Stopping(TermPath container, AStatementAtARow stops) {
            this.container = container;
            this.stops = stops;
        }

        @Override
        public AStatementAtARow.Answer at(BorderQuantity.Observation reading) {
            return switch (reading.among(container)) {
                case WalkResult.CouldNotWalk<BorderQuantity.Among> _ ->
                        new AStatementAtARow.Answer.CouldNotTell(Set.of(ReadingGap.COULD_NOT_WALK));
                case WalkResult.Reached(BorderQuantity.Among among) -> {
                    // No element chosen: the comparison is about none of them, and is made on the
                    // first application, which nothing is before.
                    if (among.chosen() == null) {
                        yield AStatementAtARow.Answer.HOLDS;
                    }
                    yield reading.keptOf(this).before(among.chosen());
                }
            };
        }

        @Override
        public Prefix readAt(BorderQuantity.Observation reading) {
            return Prefix.of(stops, reading.elementsOf(container));
        }
    }

    /**
     * What stops the operation, read on every element of one occurrence of a container: the first
     * element it certainly stops at, and each element before that where whether it stops could
     * not be read.
     *
     * <p>An element is told every reason met before it, in the order they were first met. So each
     * reason is kept once, with the first element it was met at, and the elements between hold
     * nothing of their own. The elements are read in order, so the reasons stand in the order of
     * the elements they were first met at, and what an element is told is read up to the first
     * reason met at it or after: as much as it is told, whatever was met later.
     *
     * @param stopsAt the first element it stops at, or null where it stops at none
     * @param firstAt each reason whether it stops could not be read for, in the order they were
     *                first met, with the first element it was met at
     */
    private record Prefix(Integer stopsAt, Map<ReadingGap, Integer> firstAt) {

        Prefix {
            firstAt = Collections.unmodifiableMap(new LinkedHashMap<>(firstAt));
        }

        static Prefix of(AStatementAtARow stops,
                         WalkResult<List<BorderQuantity.AnElement>> elements) {
            if (!(elements instanceof WalkResult.Reached<List<BorderQuantity.AnElement>>(
                    List<BorderQuantity.AnElement> each))) {
                // No element could be walked to, so whether any before one stopped the operation
                // is not known of any of them.
                return new Prefix(null, Map.of(ReadingGap.COULD_NOT_WALK, Integer.MIN_VALUE));
            }
            Map<ReadingGap, Integer> firstAt = new LinkedHashMap<>();
            for (BorderQuantity.AnElement one : each) {
                switch (stops.at(one.reading())) {
                    case AStatementAtARow.Answer.Holds _ -> {
                        return new Prefix(one.element(), firstAt);
                    }
                    case AStatementAtARow.Answer.Fails _ -> { }
                    case AStatementAtARow.Answer.CouldNotTell(var why) ->
                            why.forEach(gap -> firstAt.putIfAbsent(gap, one.element()));
                }
            }
            return new Prefix(null, firstAt);
        }

        /** Whether the operation got to {@code element}: no element before it stopped it. */
        AStatementAtARow.Answer before(int element) {
            if (stopsAt != null && stopsAt < element) {
                return AStatementAtARow.Answer.FAILS;
            }
            Set<ReadingGap> why = new LinkedHashSet<>();
            for (Map.Entry<ReadingGap, Integer> each : firstAt.entrySet()) {
                if (each.getValue() >= element) {
                    break;
                }
                why.add(each.getKey());
            }
            return why.isEmpty() ? AStatementAtARow.Answer.HOLDS
                    : new AStatementAtARow.Answer.CouldNotTell(why);
        }
    }
}
