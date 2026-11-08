package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.TermPath;
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
 * have made the relation at ({@link Witness#shownAt}), and at no other value: a second row is what
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
         * The values the row holds at {@code place} that a run of it is shown to have made the
         * comparison at, as the behavior's inputs are walked by {@code read} — or empty where none
         * is.
         *
         * <p>That the run went through the comparison says it was made at some value the row
         * holds there, and not at which: a walk that stops early leaves the values after it
         * unasked. So a row holding one value there shows that one, and a row holding several
         * shows all of them only where the place stands inside exactly the containers the
         * comparison is shown made on every element of ({@link #madeOnEvery}); otherwise none.
         */
        public Optional<List<ObservedValue>> shownAt(TermPath place, InputReading read) {
            BorderQuantity.Observation row = new StandingAtAPoint.DiscoveringRow(
                    new StandingAtAPoint.RowWalk(BehaviorInputs.of(read), new ObservedInputs(built,
                            new Generator.Watched.NotRun(), new AnswerObservation.NotAnswered())));
            if (!(row.everyValueAt(place)
                    instanceof WalkResult.Reached<List<ObservedValue>>(List<ObservedValue> there))
                    || there.isEmpty()) {
                return Optional.empty();
            }
            if (new LinkedHashSet<>(there).size() == 1) {
                return Optional.of(List.of(there.getFirst()));
            }
            List<TermPath> inside = new ArrayList<>();
            for (TermPath container : place.containersHoldingIt()) {
                TermPath element = container.element();
                if (!place.standsAtOrUnder(element)) {
                    return Optional.empty();
                }
                inside.add(element);
            }
            return inside.equals(madeOnEvery) ? Optional.of(List.copyOf(there))
                    : Optional.empty();
        }
    }

    /**
     * What a search for a witness came to: the row, where one was found, and where none was, the
     * figures the search stopped at before it had tried everything it would have — a run allowed
     * more may find one in the second case and never in the first.
     */
    public record Sought(Optional<Witness> found, Set<Figure> stoppedAt) {

        /** Nothing tried and nothing stopped at. */
        public static final Sought NOTHING = new Sought(Optional.empty(), Set.of());

        public Sought {
            stoppedAt = found.isPresent() ? Set.of() : Set.copyOf(stoppedAt);
        }
    }

    /**
     * The first row the search tries ({@link RowSearch}) that the boundary builds and a run of
     * which goes through the comparison {@code running} watches — or, where none is, the figures
     * the search stopped at.
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
        List<List<RowSearch.Built>> each = RowSearch.tried(inputs.types(), named, taken,
                i -> inputs.types().get(i), i -> elementOfAList(inputs.parameters().get(i), read),
                reading, building, stopped);
        if (each == null) {
            return new Sought(Optional.empty(), stopped);
        }
        for (List<RowSearch.Built> row : RowSearch.rowsOf(each, stopped)) {
            List<FixtureTemplate> fixtures = row.stream().map(RowSearch.Built::fixture).toList();
            if (running.getsThere(fixtures)) {
                return new Sought(Optional.of(new Witness(fixtures,
                        row.stream().map(RowSearch.Built::value).toList())), Set.of());
            }
        }
        return new Sought(Optional.empty(), stopped);
    }

    /** The element of the list the parameter {@code parameter} is, as the reading of the input
     *  says, or null where it is no list. */
    private static Type elementOfAList(String parameter, InputReading read) {
        TermPath at = new TermPath(parameter, List.of());
        return read.domain().holdsItsElementsInTheOrderWritten(at, read.rules())
                ? read.domain().typeAt(at.element(), read.rules()) : null;
    }
}
