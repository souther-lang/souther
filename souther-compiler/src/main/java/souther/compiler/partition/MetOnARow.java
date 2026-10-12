package souther.compiler.partition;

import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Proposition;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.IdentityHashMap;
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

    /** One container stopped short in, and what its occurrences came to on the rows asked. */
    private static final class Stopping implements Level {

        private final TermPath container;

        /** What stops the operation, put to rows. */
        private final AStatementAtARow stops;

        /** Each occurrence of the container read, by the row and what was chosen beside it. */
        private final Map<Object, Map<Map<TermPath, Integer>, Prefix>> read =
                new IdentityHashMap<>();

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
                    // The elements are read once for each occurrence and not for each reading of
                    // one: there is a reading per element, and each reading them all is the
                    // square of the container's length.
                    yield read.computeIfAbsent(among.walk(), _ -> new HashMap<>())
                            .computeIfAbsent(among.beside(), _ -> Prefix.of(stops,
                                    reading.elementsOf(container)))
                            .before(among.chosen());
                }
            };
        }
    }

    /**
     * What stops the operation, read on every element of one occurrence of a container: the first
     * element it certainly stops at, and each element before that where whether it stops could
     * not be read.
     *
     * @param stopsAt the first element it stops at, or null where it stops at none
     * @param unknown each element, in order, where it could not be read, with why
     */
    private record Prefix(Integer stopsAt, List<Map.Entry<Integer, Set<ReadingGap>>> unknown) {

        static Prefix of(AStatementAtARow stops,
                         WalkResult<List<BorderQuantity.AnElement>> elements) {
            if (!(elements instanceof WalkResult.Reached<List<BorderQuantity.AnElement>>(
                    List<BorderQuantity.AnElement> each))) {
                // No element could be walked to, so whether any before one stopped the operation
                // is not known of any of them.
                return new Prefix(null, List.of(Map.entry(Integer.MIN_VALUE,
                        Set.of(ReadingGap.COULD_NOT_WALK))));
            }
            List<Map.Entry<Integer, Set<ReadingGap>>> unknown = new ArrayList<>();
            for (BorderQuantity.AnElement one : each) {
                switch (stops.at(one.reading())) {
                    case AStatementAtARow.Answer.Holds _ -> {
                        return new Prefix(one.element(), List.copyOf(unknown));
                    }
                    case AStatementAtARow.Answer.Fails _ -> { }
                    case AStatementAtARow.Answer.CouldNotTell(var why) ->
                            unknown.add(Map.entry(one.element(), why));
                }
            }
            return new Prefix(null, List.copyOf(unknown));
        }

        /** Whether the operation got to {@code element}: no element before it stopped it. */
        AStatementAtARow.Answer before(int element) {
            if (stopsAt != null && stopsAt < element) {
                return AStatementAtARow.Answer.FAILS;
            }
            Set<ReadingGap> why = new LinkedHashSet<>();
            for (Map.Entry<Integer, Set<ReadingGap>> each : unknown) {
                if (each.getKey() < element) {
                    why.addAll(each.getValue());
                }
            }
            return why.isEmpty() ? AStatementAtARow.Answer.HOLDS
                    : new AStatementAtARow.Answer.CouldNotTell(why);
        }
    }
}
