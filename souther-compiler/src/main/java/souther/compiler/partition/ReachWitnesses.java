package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Place;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.Figure;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * A row of a behavior's inputs the boundary builds and on which the behavior answers, a run of it
 * going through the comparison the witness is asked for: a row that is shown to get to that
 * comparison, past whatever the run works out on the way.
 *
 * <p>What it shows is that row and nothing more. A relation the way to it may stop before is
 * shown reached at the values the row holds at the places it reads that a run of it is shown to
 * have made the relation at ({@link Witness#toldAt}), and at no other value: a second row is what
 * shows a second value, and no row shows every value. A reader that says what
 * the relation leaves of a place says the values shown beside what was not shown, and never
 * reads the one as the other ({@code UndividedByARelation}).
 *
 * <p>Found by the search every witness is found by ({@link RowSearch}); what is claimed is what
 * the boundary built of the row and that a run of it went through the comparison.
 */
public final class ReachWitnesses {

    private ReachWitnesses() {}

    /**
     * A row shown to get to a comparison: the fixtures it is written with, what the boundary built
     * of each, and the elements a run of it is shown to make the comparison on every one of.
     *
     * @param inputs      the row, one fixture per parameter
     * @param built       what the boundary built of each
     * @param madeOnEvery the element of each container the comparison's closures walk, outermost
     *                    first, where a run that answers and goes through the comparison once is
     *                    shown to make it on every element of each, read through the name each
     *                    closure hands it; none where that is not shown
     */
    public record Witness(List<FixtureTemplate> inputs, List<ObservedValue> built,
                          List<TermPath> madeOnEvery) {

        public Witness {
            inputs = List.copyOf(inputs);
            built = List.copyOf(built);
            madeOnEvery = List.copyOf(madeOnEvery);
            if (inputs.size() != built.size()) {
                throw new IllegalArgumentException("a row is built of each of its inputs");
            }
        }

        /** A row the search found, nothing shown of which elements a run of it made the
         *  comparison on. */
        public Witness(List<FixtureTemplate> inputs, List<ObservedValue> built) {
            this(inputs, built, List.of());
        }

        /** The same row, a run of which is shown to make the comparison on every element of each
         *  of {@code elements}. */
        public Witness madeOnEveryElementOf(List<TermPath> elements) {
            return new Witness(inputs, built, elements);
        }

        /**
         * What the row shows of a run of it having made the comparison at {@code at}, written out
         * as the model writes a value of its type: the values it holds at a position, or the
         * numbers it takes at a term of one ({@link WhatATermRead}), as the behavior's inputs are
         * walked by {@code read} — or empty where none is shown.
         *
         * <p>That the run went through the comparison says it was made at some value the row
         * holds there, and not at which: a walk that stops early leaves the values after it
         * unasked. So a row holding one value there shows that one, and a row holding several
         * shows all of them only where the place stands inside exactly the containers the
         * comparison is shown made on every element of ({@link #madeOnEvery}).
         *
         * <p>Where it does not, a place held equal to another, {@code heldEqualTo}, shows the
         * values of it that the other shows. The comparison is made at the other's value and reads
         * the place only at what is equal to it, so a value the row holds at the place that the
         * other shows is read there, whichever of the place's elements the run walked: a map's
         * entry under the key the run looked it up by. A value the other does not show is shown at
         * neither.
         *
         * <p>A term the row does not read to a number, whatever the cause, shows nothing: it is not
         * a number of zero.
         */
        public Optional<List<String>> toldAt(FilingCoordinate at,
                                             Optional<FilingCoordinate> heldEqualTo,
                                             InputReading read) {
            BorderQuantity.Observation row = observed(read);
            Optional<Held> here = heldAt(at, row, read);
            Optional<List<String>> shown = here.flatMap(this::shown);
            if (shown.isPresent() || here.isEmpty() || heldEqualTo.isEmpty()) {
                return shown;
            }
            Optional<List<String>> there = heldAt(heldEqualTo.get(), row, read)
                    .flatMap(this::shown);
            if (there.isEmpty()) {
                return Optional.empty();
            }
            List<String> both = here.get().values().stream().filter(there.get()::contains)
                    .distinct().toList();
            return both.isEmpty() ? Optional.empty() : Optional.of(both);
        }

        /**
         * Every value the row holds or takes at a coordinate, in the order the row writes them,
         * and where they stand: the place a value is held at, or the position a number is taken
         * of, and null where the number is taken over a run of values and stands at no one place.
         */
        private record Held(List<String> values, TermPath place) {}

        private Optional<Held> heldAt(FilingCoordinate at, BorderQuantity.Observation row,
                                      InputReading read) {
            return switch (at) {
                case FilingCoordinate.AtPosition(TermPath path) -> valuesAt(path, row, read);
                case FilingCoordinate.OfTerm(NumericTerm.ValueOf(TermPath position)) ->
                        valuesAt(position, row, read);
                case FilingCoordinate.OfTerm(NumericTerm term) -> numbersAt(term, row, read);
            };
        }

        private static Optional<Held> valuesAt(TermPath place, BorderQuantity.Observation row,
                                               InputReading read) {
            Type type = read.domain().typeAt(place, read.rules());
            if (type == null || !(row.everyValueAt(place)
                    instanceof WalkResult.Reached<List<ObservedValue>>(List<ObservedValue> there))
                    || there.isEmpty()) {
                return Optional.empty();
            }
            RuleReadingContext reading = RuleReadingContext.of(read.rules(),
                    read.domain().policy(), read.domain().machines(), read.domain().today());
            List<String> out = new ArrayList<>();
            for (ObservedValue each : there) {
                if (!(ObservedFixtures.of(each, type, reading)
                        instanceof ObservedFixtures.Writing.Written<FixtureTemplate>(
                                FixtureTemplate fixture))) {
                    return Optional.empty();
                }
                out.add(fixture.text());
            }
            return Optional.of(new Held(out, place));
        }

        private static Optional<Held> numbersAt(NumericTerm term, BorderQuantity.Observation row,
                                                InputReading read) {
            TermOrders orders = read.quantities().ordersOf(term);
            if (orders == null || orders.answered() == null
                    || !(term instanceof NumericTerm.FromOnePosition
                    || term instanceof NumericTerm.TakenOver)) {
                return Optional.empty();
            }
            TermPath position = term instanceof NumericTerm.FromOnePosition one
                    ? one.position() : null;
            List<Place> there = new ArrayList<>();
            List<TermPath> containers = position == null ? List.of()
                    : position.containersHoldingIt();
            if (!numbersAt(row, containers, orders, there) || there.isEmpty()) {
                return Optional.empty();
            }
            return Optional.of(new Held(there.stream().map(orders.answered()::written).toList(),
                    position));
        }

        private BorderQuantity.Observation observed(InputReading read) {
            return new StandingAtAPoint.DiscoveringRow(
                    new StandingAtAPoint.RowWalk(BehaviorInputs.of(read), new ObservedInputs(built,
                            new Generator.Watched.NotRun(), new AnswerObservation.NotAnswered())));
        }

        /** What a run of the row is shown to have made the comparison at, of what the row holds
         *  or takes there. */
        private Optional<List<String>> shown(Held held) {
            List<String> there = held.values();
            TermPath place = held.place();
            if (new LinkedHashSet<>(there).size() == 1) {
                return Optional.of(List.of(there.getFirst()));
            }
            List<TermPath> inside = new ArrayList<>();
            if (place != null) {
                for (TermPath container : place.containersHoldingIt()) {
                    TermPath element = container.element();
                    if (!place.standsAtOrUnder(element)
                            && !place.standsAtOrUnder(container.key())) {
                        return Optional.empty();
                    }
                    inside.add(element);
                }
            }
            return inside.equals(madeOnEvery) ? Optional.of(List.copyOf(there))
                    : Optional.empty();
        }

        /** Adds to {@code out} the number {@code orders} reads at each element of the
         *  {@code containers}, outermost first; false where some is not read to a number. */
        private static boolean numbersAt(BorderQuantity.Observation row,
                                         List<TermPath> containers, TermOrders orders,
                                         List<Place> out) {
            if (containers.isEmpty()) {
                if (!(WhatATermRead.ofTerm(orders, row) instanceof WhatATermRead.Number(
                        Place number))) {
                    return false;
                }
                out.add(number);
                return true;
            }
            if (!(row.eachElementOf(containers.getFirst())
                    instanceof WalkResult.Reached<List<BorderQuantity.Observation>>(
                            List<BorderQuantity.Observation> each))) {
                return false;
            }
            for (BorderQuantity.Observation element : each) {
                if (!numbersAt(element, containers.subList(1, containers.size()), orders, out)) {
                    return false;
                }
            }
            return true;
        }
    }

    /**
     * What a search for a witness came to: the row, where one was found, and where none was, the
     * figures the search stopped at before it had tried everything it would have — a run allowed
     * more may find one in the second case and never in the first — and where the runs of the
     * rows it tried stopped without answering, as a count's search says them
     * ({@link CountWitnesses.Sought#runsStopped}): each is an input the model has not decided
     * about, and no run allowed more gets past it.
     *
     * @param found       the row, or empty
     * @param stoppedAt   the figures the search stopped at, none where a row was found
     * @param runsStopped where the runs of the rows tried stopped, each once, none where a row was
     *                    found
     */
    public record Sought(Optional<Witness> found, Set<Figure> stoppedAt,
                         Set<WhereARunStopped> runsStopped) {

        /** Nothing tried and nothing stopped at. */
        public static final Sought NOTHING = new Sought(Optional.empty(), Set.of(), Set.of());

        public Sought {
            stoppedAt = found.isPresent() ? Set.of() : Set.copyOf(stoppedAt);
            runsStopped = found.isPresent() ? Set.of() : Set.copyOf(runsStopped);
        }

        /** The same search, its row shown to make the comparison on every element of each of
         *  {@code elements} ({@link Witness#madeOnEveryElementOf}). */
        public Sought madeOnEveryElementOf(List<TermPath> elements) {
            return new Sought(found.map(row -> row.madeOnEveryElementOf(elements)), stoppedAt,
                    runsStopped);
        }
    }

    /**
     * The first row the search tries ({@link RowSearch}) that the boundary builds and a run of
     * which goes through the comparison {@code running} watches — or, where none is, the figures
     * the search stopped at and where the runs of the rows it tried stopped.
     *
     * @param named the values the model names at each parameter's type
     * @param taken what each row written for the behavior took, one value per parameter
     */
    public static Sought of(InputReading read, List<List<FixtureTemplate>> named,
                            List<List<ObservedValue>> taken, RowSearch.Building building,
                            RowSearch.Running running) {
        BehaviorInputs inputs = BehaviorInputs.of(read);
        RuleReadingContext reading = RuleReadingContext.of(read.rules(), read.domain().policy(),
                read.domain().machines(), read.domain().today());
        Set<Figure> stopped = new LinkedHashSet<>();
        Set<WhereARunStopped> runs = new LinkedHashSet<>();
        List<List<RowSearch.Built>> each = RowSearch.tried(inputs.types(), named, taken,
                i -> inputs.types().get(i), i -> elementOfAList(inputs.parameters().get(i), read),
                reading, building, stopped);
        if (each == null) {
            return new Sought(Optional.empty(), stopped, runs);
        }
        for (List<RowSearch.Built> row : RowSearch.rowsOf(each, stopped)) {
            List<FixtureTemplate> fixtures = row.stream().map(RowSearch.Built::fixture).toList();
            RowSearch.Run ran = running.run(fixtures);
            if (ran.getsThere()) {
                return new Sought(Optional.of(new Witness(fixtures,
                        row.stream().map(RowSearch.Built::value).toList())), Set.of(), Set.of());
            }
            ran.stopped().ifPresent(runs::add);
        }
        return new Sought(Optional.empty(), stopped, runs);
    }

    /** The element of the list the parameter {@code parameter} is, as the reading of the input
     *  says, or null where it is no list. */
    private static Type elementOfAList(String parameter, InputReading read) {
        TermPath at = new TermPath(parameter, List.of());
        return read.domain().holdsItsElementsInTheOrderWritten(at, read.rules())
                ? read.domain().typeAt(at.element(), read.rules()) : null;
    }
}
