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

    /** Each container stopped short in, the outermost first, as what is put to a row. */
    private final List<Level> levels;

    /** What a reading of no element can say, where this is not said at all. */
    private final ReadingGap notSaid;

    private MetOnARow(List<Level> levels, ReadingGap notSaid) {
        this.levels = levels;
        this.notSaid = notSaid;
    }

    /** {@code metOn}, ready to be put to the readings of a behavior's rows. */
    static MetOnARow of(ElementsMetOn metOn, String behavior, Quantities quantities) {
        return switch (metOn) {
            case ElementsMetOn.NotSaid(ReadingGap why) -> new MetOnARow(List.of(), why);
            case ElementsMetOn.InOrder(var stopping) -> {
                List<Level> levels = new ArrayList<>();
                for (ElementsMetOn.StopsAt each : stopping) {
                    levels.add(new Level(each.container(),
                            AStatementAtARow.askable(each.stops())
                                    ? AStatementAtARow.of(each.stops(), behavior, quantities)
                                    : null,
                            unasked(each.stops())));
                }
                yield new MetOnARow(List.copyOf(levels), null);
            }
        };
    }

    /** Why {@code stops} cannot be put to a row: a part of it nothing read, or a part no value
     *  of a row settles. */
    private static ReadingGap unasked(Proposition stops) {
        return ReadingGap.ReachNotRead.of(Proposition.firstStopIn(stops));
    }

    /**
     * Whether a run that got as far as the comparison made it on the elements {@code reading}
     * names.
     *
     * <p>Not made in some container settles it, whatever else is not known: a run that stopped
     * before the element in one container never got to the closure inside it.
     */
    AStatementAtARow.Answer at(BorderQuantity.Observation reading) {
        if (notSaid != null) {
            return new AStatementAtARow.Answer.CouldNotTell(Set.of(notSaid));
        }
        Set<ReadingGap> unknown = new LinkedHashSet<>();
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

    /** One container stopped short in, and what its occurrences came to on the rows asked. */
    private static final class Level {

        private final TermPath container;

        /** What stops the operation, put to rows; null where it cannot be. */
        private final AStatementAtARow stops;

        /** Why it cannot be, where it cannot. */
        private final ReadingGap unread;

        /** Each occurrence of the container read, by the row and what was chosen beside it. */
        private final Map<Object, Map<Map<TermPath, Integer>, Prefix>> read =
                new IdentityHashMap<>();

        Level(TermPath container, AStatementAtARow stops, ReadingGap unread) {
            this.container = container;
            this.stops = stops;
            this.unread = unread;
        }

        AStatementAtARow.Answer at(BorderQuantity.Observation reading) {
            return switch (reading.among(container)) {
                case WalkResult.CouldNotWalk<BorderQuantity.Among> _ ->
                        new AStatementAtARow.Answer.CouldNotTell(Set.of(ReadingGap.COULD_NOT_WALK));
                case WalkResult.Reached(BorderQuantity.Among among) -> {
                    // No element chosen: the comparison is about none of them, and is made on the
                    // first application, which nothing is before.
                    if (among.chosen() == null) {
                        yield AStatementAtARow.Answer.HOLDS;
                    }
                    if (stops == null) {
                        yield among.elements().indexOf(among.chosen()) == 0
                                ? AStatementAtARow.Answer.HOLDS
                                : new AStatementAtARow.Answer.CouldNotTell(Set.of(unread));
                    }
                    yield read.computeIfAbsent(among.walk(), _ -> new HashMap<>())
                            .computeIfAbsent(among.beside(), _ -> Prefix.of(stops, among))
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

        static Prefix of(AStatementAtARow stops, BorderQuantity.Among among) {
            List<Map.Entry<Integer, Set<ReadingGap>>> unknown = new ArrayList<>();
            for (int at = 0; at < among.elements().size(); at++) {
                int element = among.elements().get(at);
                switch (stops.at(among.each().get(at))) {
                    case AStatementAtARow.Answer.Holds _ -> {
                        return new Prefix(element, List.copyOf(unknown));
                    }
                    case AStatementAtARow.Answer.Fails _ -> { }
                    case AStatementAtARow.Answer.CouldNotTell(var why) ->
                            unknown.add(Map.entry(element, why));
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
