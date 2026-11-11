package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.Distinctions;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.PositionsAStatementReads;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.numeric.CountDomain;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.observe.Figure;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;

/**
 * A row of a behavior's inputs at which a counted statement holds of one element of the container
 * and fails of another, beside one and the same value of everything else the behavior takes — and
 * at which the behavior answers, the run going through the comparison it is asked for.
 *
 * <p>Found and then shown. Which values are tried is a search ({@link RowSearch}), and a search may
 * miss: a named value of a parameter's type the model writes ({@code TypedFixtureValues}), what
 * stands for each type ({@link Partitions#representativesOf}), and an element made to hold, at the
 * place a statement says is the same value as a place outside the container, each value the row
 * holds there. None of that is a claim. What is a claim is what the boundary built of the row
 * ({@link RowSearch.Building}), what the statement says of each element of what it built
 * ({@link AStatementAtARow#howManyMeetIn}) — one element it holds of and one it fails of, and none
 * it could not tell — and that the behavior answered on it, a run of it going through the
 * comparison ({@link RowSearch.Running}). A row the search did not find is no row shown not to
 * exist.
 *
 * <p>A witness is of one comparison as well as of one count: the way to a comparison may ask
 * something of what the row holds beside the container, and a row that meets the statement both
 * ways and answers somewhere else shows nothing of that comparison. What the reading of the
 * comparison makes of the witness — every count of every size — is that reading's
 * ({@code UndividedByARelation}).
 */
public final class CountWitnesses {

    /** How many of a parameter's values are tried before the search stops. */
    private static final int MOST_VALUES = RowSearch.MOST_VALUES;

    private CountWitnesses() {}

    /**
     * What a search for a witness came to: the witness, where one was found, and where none was,
     * the figures the search stopped at before it had tried everything it would have, and where
     * the runs of the rows it tried stopped without answering.
     *
     * <p>Three misses apart, and each leaves the count not shown. A search that tried all it had
     * and found nothing is met again by a run allowed more. One that stopped at a figure may find a
     * witness in such a run, and the figure is what says so. And one whose rows met the statement
     * both ways and whose runs on them stopped — at an invariant a construction did not keep, an
     * {@code ensures} the answer did not keep, an operation the runtime would not finish, an
     * {@code unreachable} — is met again by a run allowed more too, and where the runs stopped is
     * what an author goes to: each is an input the model has not decided about.
     *
     * @param found       the witness, or empty
     * @param stoppedAt   the figures the search stopped at, none where one was found: its own, and
     *                    any a value it would have tried was cut short at before it got it
     * @param runsStopped where the runs of the rows tried stopped, each once, none where a witness
     *                    was found
     */
    public record Sought(Optional<Witness> found, Set<Figure> stoppedAt,
                         Set<WhereARunStopped> runsStopped) {

        /** Nothing tried and nothing stopped at. */
        public static final Sought NOTHING = new Sought(Optional.empty(), Set.of(), Set.of());

        public Sought {
            stoppedAt = found.isPresent() ? Set.of() : Set.copyOf(stoppedAt);
            runsStopped = found.isPresent() ? Set.of() : Set.copyOf(runsStopped);
        }
    }

    /**
     * What a count of a container's elements asks of each element, and which value of it is
     * counted: the statement the elements meet, and where the count is of different values and
     * not of elements, the place the values are taken at.
     *
     * @param container   where the container is a parameter's own, no step under it
     * @param statement   what an element is asked: the statement counted of a count of elements
     *                    that meet it, what keeps an element of a count of the values of those a
     *                    statement keeps, and nothing of a count of every element's value
     * @param differentAt where the values counted stand, empty where elements are counted
     */
    record Asked(TermPath container, Proposition statement,
                 Optional<Quantity.TheValue> differentAt) {

        /**
         * What {@code count} asks, or null where it is not of the elements of a container a
         * parameter holds, or keeps its elements by what the elements holding a value come to,
         * which no one element answers.
         */
        static Asked of(Quantity.CountedOverAContainer count) {
            if (!(count.container() instanceof DecisionSubject.AnInput(TermPath container, var _))
                    || !container.steps().isEmpty()) {
                return null;
            }
            return switch (count) {
                case Quantity.HowManyMeet meet ->
                        new Asked(container, meet.statement(), Optional.empty());
                case Quantity.HowManyDifferent different ->
                        new Asked(container, different.statement(),
                                Optional.of(different.ofTheElement()));
                case Quantity.HowManyDifferentMeet different
                        when !different.across() && different.meeting()
                                instanceof Quantity.HowManyDifferentMeet.Selection.OfEachElement ->
                        new Asked(container, different.statement(),
                                Optional.of(different.ofTheElement()));
                case Quantity.HowManyDifferentMeet _ -> null;
            };
        }

        /** The places the values counted are taken at, none where elements are counted. */
        List<TermPath> valuePlaces() {
            return differentAt.map(Quantity.TheValue::places).orElse(List.of());
        }

        /** Every place the count reads of an element or outside the container: what the statement
         *  reads and where the values stand — or empty where the statement is not read through. */
        Optional<List<TermPath>> reads() {
            return PositionsAStatementReads.of(statement).map(read -> {
                List<TermPath> out = new ArrayList<>(read);
                valuePlaces().stream().filter(place -> !out.contains(place)).forEach(out::add);
                return out;
            });
        }
    }

    /**
     * The row shown: every input, with the container holding two elements that tell the count
     * apart — for a count of the elements that meet a statement, one it holds of and then one it
     * fails of; for a count of different values, two that the statement keeps and that hold
     * different values.
     *
     * @param inputs    the row, one fixture per parameter
     * @param container which parameter is the container
     * @param one       the first of the two
     * @param other     the second
     * @param failing   an element the statement fails of that the boundary builds a container of,
     *                  or null where none was found — or where nothing is asked of an element, so
     *                  that there is none to fail
     * @param overAgain whether the container is a list, which may hold an element over again, so
     *                  that a row holds the one the statement holds of as many times as it likes
     *                  and the count takes every value up to its size; a container that holds each
     *                  element once shows no more than the one. It is the type's, and no rule's:
     *                  a rule that keeps a list's elements apart leaves it fewer to hold, which is
     *                  what {@code UndividedByARelation#howManyAreHeld} says of it, and a count is
     *                  shown only as far as that
     */
    public record Witness(List<FixtureTemplate> inputs, int container, FixtureTemplate one,
                          FixtureTemplate other, FixtureTemplate failing, boolean overAgain) {

        public Witness {
            inputs = List.copyOf(inputs);
        }
    }

    /**
     * A row at which {@code count}'s statement holds of one element and fails of another, the
     * behavior answering — or, for a count of different values, a row whose container holds two
     * elements the statement keeps that hold different values — or, where none was found, the
     * figures the search stopped at first and where the runs of the rows it tried stopped.
     *
     * <p>Only of a count of a parameter's own elements, of a list or a set. Where it is a list the
     * rows a count is read over hold the witness's elements so many times each; a set holds each
     * once, and what the witness shows of it is the one element and the other
     * ({@link Witness#overAgain}).
     *
     * @param named the values the model names at each parameter's type, tried before anything
     *              else is
     * @param taken what each row written for the behavior took, one value per parameter, as its
     *              run held it: tried next, each written back from what was built, and the
     *              elements of the container among them tried before what stands for the element
     */
    public static Sought of(Quantity.CountedOverAContainer count, String behavior,
                            InputReading read, List<List<FixtureTemplate>> named,
                            List<List<ObservedValue>> taken, RowSearch.Building building,
                            RowSearch.Running running) {
        Asked asked = Asked.of(count);
        if (asked == null) {
            return Sought.NOTHING;
        }
        TermPath container = asked.container();
        // A list may hold an element over again, which is how it is held to the fewest elements
        // its rules ask; a set holds each once, and what one element meets and another fails are
        // two values already.
        boolean repeats = read.domain().holdsAnElementOverAgain(container, read.rules());
        if (!repeats && !read.domain().holdsEachElementOnce(container, read.rules())) {
            return Sought.NOTHING;
        }
        BehaviorInputs inputs = BehaviorInputs.of(read);
        int at = inputs.parameters().indexOf(container.head());
        Type element = read.domain().typeAt(container.element(), read.rules());
        if (at < 0 || element == null) {
            return Sought.NOTHING;
        }
        RuleReadingContext reading = RuleReadingContext.of(read.rules(), read.domain().policy(),
                read.domain().machines(), read.domain().today());
        AStatementAtARow statement = AStatementAtARow.of(asked.statement(), behavior,
                read.quantities());
        // The container as the parameter it is: a list a newtype wraps is written as the newtype.
        RuleReadingSource source = reading.source();
        TypeView parameter = inputs.viewOf(inputs.types().get(at));
        // Whether its names can be written is the type's, so a container whose names cannot be has
        // no row to show.
        List<TypeSymbol> worn = parameter.wrappers();
        if (!(WornNames.of(worn, source) instanceof WornNames.Spelled spelled)) {
            return Sought.NOTHING;
        }
        Set<Figure> stopped = new LinkedHashSet<>();
        Set<WhereARunStopped> runs = new LinkedHashSet<>();
        // What each parameter may hold, as far as the boundary builds it, the container as the
        // parameter it is: a candidate of a bare list is no value of a parameter that wears a name
        // or a rule, and the boundary refuses it. The elements tried below take the place of what
        // the container holds.
        // Every parameter is tried at all its values: what the statement counted turns on may name
        // a parameter the body does not read, and no one has said which are named.
        Set<String> readOutside = new LinkedHashSet<>();
        PositionsAStatementReads.of(asked.statement()).orElse(List.of()).stream()
                .filter(place -> !place.head().equals(container.head()))
                .forEach(place -> readOutside.add(place.head()));
        List<List<RowSearch.Built>> each = RowSearch.tried(inputs.types(), named, taken,
                inputs.types()::get,
                i -> readOutside.contains(inputs.parameters().get(i)), _ -> false, reading,
                building, stopped);
        if (each == null) {
            return new Sought(Optional.empty(), stopped, runs);
        }
        // And the elements the model writes in the container, each written back as a fixture of
        // the element's type, tried before what stands for that type.
        List<FixtureTemplate> written = new ArrayList<>();
        for (RowSearch.Built list : each.get(at)) {
            elementsOf(ObservedValue.inside(worn, list.value()), element, reading, written,
                    stopped);
        }
        Container holder = new Container(at, container, spelled::holding, worn,
                repeats ? fewestHeld(container, read) : 1, repeats);
        each.set(at, each.get(at).subList(0, 1));
        // The rows of those, nearest first, as many as the search tries: one whose other values
        // leave no element to hold the statement of and another to fail it is no row shown that
        // none does, so the next is tried.
        for (List<RowSearch.Built> row : RowSearch.rowsOf(each, stopped)) {
            Optional<Witness> found = beside(row, holder, element, asked, inputs, statement,
                    reading, building, running, written, stopped, runs);
            if (found.isPresent()) {
                return new Sought(found, Set.of(), Set.of());
            }
        }
        return new Sought(Optional.empty(), stopped, runs);
    }

    /** Adds to {@code into} each element of {@code list}, a container the boundary built, written
     *  back as a fixture of {@code element}, where it is one, and each once — and to
     *  {@code stopped} the figure it was cut short at, where it was. */
    private static void elementsOf(ObservedValue list, Type element, RuleReadingContext reading,
                                   List<FixtureTemplate> into, Set<Figure> stopped) {
        if (list instanceof ObservedValue.Truncated(Figure cut)) {
            stopped.add(cut);
        }
        if (!(list instanceof ObservedValue.Sequence(List<ObservedValue> held))) {
            return;
        }
        for (ObservedValue each : held) {
            if (ObservedFixtures.of(each, element, reading)
                    instanceof ObservedFixtures.Writing.Written<FixtureTemplate>(
                            FixtureTemplate fixture)
                    && !into.contains(fixture)) {
                into.add(fixture);
            }
        }
    }

    /** A witness whose other inputs are {@code beside}'s, or empty where none was found there —
     *  and, where the run of the row that met the statement both ways stopped, where it did,
     *  added to {@code runs}. */
    private static Optional<Witness> beside(List<RowSearch.Built> beside, Container container,
                                            Type element, Asked asked, BehaviorInputs inputs,
                                            AStatementAtARow statement,
                                            RuleReadingContext reading,
                                            RowSearch.Building building,
                                            RowSearch.Running running,
                                            List<FixtureTemplate> written,
                                            Set<Figure> stopped, Set<WhereARunStopped> runs) {
        List<FixtureTemplate> row = beside.stream().map(RowSearch.Built::fixture).toList();
        List<ObservedValue> built = beside.stream().map(RowSearch.Built::value).toList();
        List<FixtureTemplate> tried = elementsTried(element, container, asked, inputs, built,
                reading, building, written, stopped);
        boolean ofValues = asked.differentAt().isPresent();
        List<FixtureTemplate> both = ofValues
                ? twoThatDiffer(tried, container, asked.differentAt().get(), built, inputs,
                        statement, building)
                : oneKeptAndOneDropped(tried, container, built, inputs, statement, building);
        if (both == null) {
            return Optional.empty();
        }
        // What fails the statement is the second of a count of elements; of a count of values it is
        // one more element, which none is where every element meets the statement.
        FixtureTemplate failing = ofValues
                ? aFailingElement(tried, container, built, inputs, statement, building)
                : both.getLast();
        List<FixtureTemplate> shown = new ArrayList<>(row);
        shown.set(container.at(), container.holding(both));
        RowSearch.Run ran = running.run(shown);
        if (!ran.getsThere()) {
            ran.stopped().ifPresent(runs::add);
            return Optional.empty();
        }
        return Optional.of(new Witness(shown, container.at(), both.getFirst(), both.getLast(),
                failing, container.overAgain()));
    }

    /**
     * An element of {@code tried} the statement fails of, in a container the boundary builds of it
     * alone — or null where there is none.
     */
    private static FixtureTemplate aFailingElement(List<FixtureTemplate> tried,
                                                   Container container, List<ObservedValue> built,
                                                   BehaviorInputs inputs,
                                                   AStatementAtARow statement,
                                                   RowSearch.Building building) {
        for (FixtureTemplate each : tried) {
            Integer meet = metIn(List.of(each), container, built, inputs, statement, building);
            if (meet != null && meet == 0) {
                return each;
            }
        }
        return null;
    }

    /**
     * An element of {@code tried} the statement holds of and one it fails of, in a container that
     * holds both and the statement holds of one of — or null where there are not both.
     */
    private static List<FixtureTemplate> oneKeptAndOneDropped(List<FixtureTemplate> tried,
                                                              Container container,
                                                              List<ObservedValue> built,
                                                              BehaviorInputs inputs,
                                                              AStatementAtARow statement,
                                                              RowSearch.Building building) {
        FixtureTemplate kept = null;
        FixtureTemplate dropped = null;
        for (FixtureTemplate each : tried) {
            Integer meet = metIn(List.of(each), container, built, inputs, statement, building);
            if (meet == null) {
                continue;
            }
            // The container holds the element over again where a rule asks for more than one, so
            // it holds the statement of all of them or of none.
            if (meet == container.filled(List.of(each)).size() && kept == null) {
                kept = each;
            } else if (meet == 0 && dropped == null) {
                dropped = each;
            }
            if (kept != null && dropped != null) {
                break;
            }
        }
        if (kept == null || dropped == null) {
            return null;
        }
        List<FixtureTemplate> both = List.of(kept, dropped);
        Integer meet = metIn(both, container, built, inputs, statement, building);
        return meet == null || meet != 1 ? null : both;
    }

    /**
     * Two elements of {@code tried} the statement holds of, in a container that holds both and
     * whose elements hold two different values at {@code at} — or null where there are no two.
     * Asked of the container itself, as the count is, so that what the two are is what the row
     * counts.
     */
    private static List<FixtureTemplate> twoThatDiffer(List<FixtureTemplate> tried,
                                                       Container container,
                                                       Quantity.TheValue at,
                                                       List<ObservedValue> built,
                                                       BehaviorInputs inputs,
                                                       AStatementAtARow statement,
                                                       RowSearch.Building building) {
        List<FixtureTemplate> kept = new ArrayList<>();
        for (FixtureTemplate each : tried) {
            Integer meet = metIn(List.of(each), container, built, inputs, statement, building);
            if (meet != null && meet == container.filled(List.of(each)).size()) {
                kept.add(each);
            }
        }
        // Holding the same value is an equivalence, so two that differ exist exactly where some
        // element differs from the first: each is asked of it alone.
        for (int other = 1; other < kept.size(); other++) {
            List<FixtureTemplate> both = List.of(kept.getFirst(), kept.get(other));
            Integer different = differentIn(both, container, at, built, inputs, statement,
                    building);
            if (different != null && different == 2) {
                return both;
            }
        }
        return null;
    }

    /**
     * How many different values the elements {@code elements} hold at {@code at}, in a row
     * otherwise {@code built}, among those the statement holds of — or null where the boundary
     * refused the container, or the statement or a value could not be read of some element.
     */
    private static Integer differentIn(List<FixtureTemplate> elements, Container container,
                                       Quantity.TheValue at, List<ObservedValue> built,
                                       BehaviorInputs inputs, AStatementAtARow statement,
                                       RowSearch.Building building) {
        Optional<ObservedValue> held = building.build(container.at(),
                container.holding(elements));
        if (held.isEmpty()) {
            return null;
        }
        List<ObservedValue> values = new ArrayList<>(built);
        values.set(container.at(), held.get());
        AStatementAtARow.HowManyAtARow counted = statement.howManyIn(container.place(),
                Optional.of(at), Optional.empty(),
                new StandingAtAPoint.DiscoveringRow(new StandingAtAPoint.RowWalk(inputs,
                        new ObservedInputs(values, new Generator.Watched.NotRun(),
                                new AnswerObservation.NotAnswered()))));
        return counted == null || counted.unread() != 0 ? null : counted.meet();
    }

    /**
     * How many of the container's elements in the row {@code inputs} the statement {@code count}
     * counts holds of — or empty where the boundary refused some input, or the statement could not
     * tell of some element. The reading a witness is held to, for a row written out.
     */
    public static Optional<Integer> metOn(Quantity.HowManyMeet count, String behavior,
                                          InputReading read, List<FixtureTemplate> inputs,
                                          RowSearch.Building building) {
        if (!(count.container() instanceof DecisionSubject.AnInput(TermPath container, var _))
                || !container.steps().isEmpty()) {
            return Optional.empty();
        }
        BehaviorInputs of = BehaviorInputs.of(read);
        List<ObservedValue> built = new ArrayList<>();
        for (int i = 0; i < inputs.size(); i++) {
            Optional<ObservedValue> made = building.build(i, inputs.get(i));
            if (made.isEmpty()) {
                return Optional.empty();
            }
            built.add(made.get());
        }
        return Optional.ofNullable(counted(built, of, AStatementAtARow.of(count.ofTheElement(),
                behavior, read.quantities()), container));
    }

    /** How many of the container's elements in a row of {@code built} the statement holds of, or
     *  null where it could not tell of some element. */
    private static Integer counted(List<ObservedValue> built, BehaviorInputs inputs,
                                   AStatementAtARow statement, TermPath container) {
        AStatementAtARow.HowManyAtARow counted = statement.howManyMeetIn(container,
                new StandingAtAPoint.DiscoveringRow(new StandingAtAPoint.RowWalk(inputs,
                        new ObservedInputs(built, new Generator.Watched.NotRun(),
                                new AnswerObservation.NotAnswered()))));
        return counted == null || counted.unread() != 0 ? null : counted.meet();
    }

    /**
     * How many of {@code elements}, the container's elements in a row otherwise {@code row}, the
     * statement holds of — or null where the boundary refused the container, or the statement
     * could not tell of some element.
     */
    private static Integer metIn(List<FixtureTemplate> elements, Container container,
                                 List<ObservedValue> built, BehaviorInputs inputs,
                                 AStatementAtARow statement, RowSearch.Building building) {
        Optional<ObservedValue> held = building.build(container.at(),
                container.holding(elements));
        if (held.isEmpty()) {
            return null;
        }
        List<ObservedValue> values = new ArrayList<>(built);
        values.set(container.at(), held.get());
        return counted(values, inputs, statement, container.place());
    }

    /**
     * The elements tried: those the model writes in the container ({@code inTheRows}), what stands
     * for the element's type, and each of the latter made to hold, at a place the statement says
     * is the same value as a place outside the container, every value the row holds there.
     */
    private static List<FixtureTemplate> elementsTried(Type element, Container held, Asked asked,
                                                       BehaviorInputs inputs,
                                                       List<ObservedValue> built,
                                                       RuleReadingContext reading,
                                                       RowSearch.Building building,
                                                       List<FixtureTemplate> inTheRows,
                                                       Set<Figure> stopped) {
        TermPath container = held.place();
        Proposition stated = asked.statement();
        // In the order they are tried, and held to the figure once, over all of them: where they
        // come from decides which are tried first and never whether the figure applies.
        List<FixtureTemplate> standing = Partitions.representativesOf(element, reading).values();
        List<FixtureTemplate> out = new ArrayList<>(inTheRows);
        out.addAll(standing);
        Map<List<String>, TermPath> alike = new LinkedHashMap<>();
        sameValuesIn(stated, container.element(), alike);
        if (out.size() > MOST_VALUES) {
            return RowSearch.upTo(out, stopped);
        }
        if (alike.isEmpty()) {
            return RowSearch.upTo(withWhatItReadsDiffering(out, element, container, asked,
                    reading, stopped), stopped);
        }
        BorderQuantity.Observation row = new StandingAtAPoint.DiscoveringRow(
                new StandingAtAPoint.RowWalk(inputs, new ObservedInputs(built,
                        new Generator.Watched.NotRun(), new AnswerObservation.NotAnswered())));
        making:
        for (FixtureTemplate base : standing) {
            ObservedValue each = builtAlone(base, held, building);
            if (each == null) {
                continue;
            }
            for (Map.Entry<List<String>, TermPath> place : alike.entrySet()) {
                if (!(row.everyValueAt(place.getValue())
                        instanceof WalkResult.Reached<List<ObservedValue>>(var there))) {
                    continue;
                }
                for (ObservedValue value : there) {
                    ObservedValue moved = withAt(each, place.getKey(), value);
                    if (moved != null && ObservedFixtures.of(moved, element, reading)
                            instanceof ObservedFixtures.Writing.Written<FixtureTemplate>(
                                    FixtureTemplate written)) {
                        out.add(written);
                        // One past what is tried is enough to know the figure is reached, and
                        // nothing past it is built.
                        if (out.size() > MOST_VALUES) {
                            break making;
                        }
                    }
                }
            }
        }
        return RowSearch.upTo(withWhatItReadsDiffering(out, element, container, asked, reading,
                stopped), stopped);
    }

    /**
     * {@code tried}, then the element with each place {@code stated} reads inside it at each of the
     * values its type tells apart, and everything else as the rules admit: the elements a
     * statement may tell apart by a place of their own, which the one value that stands for the
     * element does not. After what was tried, so that a row found without them is the row found.
     *
     * <p>A place is the element itself where the statement is about the element and not a field
     * of it ({@code x -> x}), which is the empty run of fields.
     *
     * <p>A type that states a division — both of a {@code Bool}, each case of a sum — is taken at
     * every value that divides it, and any other at two values that differ
     * ({@link Witnesses#distinctValuesOf}): one a statement holds of and one it fails of is what
     * is looked for, and a type with no division of its own has no more than that to tell apart.
     * And at the values the statement itself names there ({@link ValuesAStatementNames}), written
     * as the type of the place writes them, which are what it tells apart where the type tells
     * nothing.
     *
     * <p>What this finds is the elements a statement turns on the values it names and the types
     * divide into tell apart. Where it turns on anything else — a measure of a place, what two
     * places add up to — the element is found where a row of the model supplies it, and nothing is
     * found otherwise.
     */
    private static List<FixtureTemplate> withWhatItReadsDiffering(
            List<FixtureTemplate> tried, Type element, TermPath container, Asked asked,
            RuleReadingContext reading, Set<Figure> stopped) {
        RuleReadingSource source = reading.source();
        Map<TermPath, List<ValuesAStatementNames.Named>> named =
                ValuesAStatementNames.of(asked.statement());
        Map<List<String>, List<FixtureTemplate>> told = new LinkedHashMap<>();
        for (TermPath place : asked.reads().orElse(List.of())) {
            List<String> fields = fieldsBelow(container.element(), place);
            Type type = fields == null ? null : Witnesses.typeAt(element, fields, reading);
            if (type == null) {
                continue;
            }
            int divided = Distinctions.ofType(TypeView.shapeOf(type, source.inners(),
                    source.symbols(), source.kinds(), source.sums()), source.symbols(),
                    source.kinds(), source.sums()).size();
            List<FixtureTemplate> values = new ArrayList<>(Witnesses.distinctValuesOf(type,
                    valuesAskedOfAType(divided), reading, Set.of()).values());
            for (ValuesAStatementNames.Named each : named.getOrDefault(place, List.of())) {
                if (!RowSearch.hasRoom(values)) {
                    break;
                }
                FixtureTemplate written = switch (each) {
                    case ValuesAStatementNames.Named.Numeric number ->
                            Partitions.writtenNumberAt(type, number.at(), reading);
                    case ValuesAStatementNames.Named.Written text ->
                            Witnesses.writtenAs(text.at(), type, reading);
                    case ValuesAStatementNames.Named.Holding many ->
                            Witnesses.holdingMany(type, many.many(), reading);
                };
                if (written != null && !values.contains(written)) {
                    values.add(written);
                }
            }
            if (!values.isEmpty()) {
                told.putIfAbsent(fields, RowSearch.upTo(values, stopped));
            }
        }
        List<FixtureTemplate> out = new ArrayList<>(tried);
        for (Map<List<String>, FixtureTemplate> placed : waysTheyCanBeTogether(told, stopped)) {
            for (FixtureTemplate one : Witnesses.holdingAt(element, placed, reading).values()) {
                if (!out.contains(one)) {
                    out.add(one);
                }
                break;
            }
        }
        return out;
    }

    /**
     * How many values are asked of a type that divides its values into {@code divided} kinds: one
     * of each, and two at least, since one a statement holds of and one it fails of is what is
     * looked for — and no more than one past the figure, which says it was passed.
     */
    static int valuesAskedOfAType(int divided) {
        return Math.min(Math.max(2, divided), MOST_VALUES + 1);
    }

    /**
     * Each place of {@code told} at each of its values alone, then every place at once — a
     * statement over two of them holds only where both are at the values it asks for — as many as
     * the figure the elements are tried to ({@link RowSearch#MOST_VALUES}), with the figure said in
     * {@code stopped} where there are more. The ways together are counted and then made one at a
     * time, so that nothing past the figure is built.
     */
    private static List<Map<List<String>, FixtureTemplate>> waysTheyCanBeTogether(
            Map<List<String>, List<FixtureTemplate>> told, Set<Figure> stopped) {
        List<List<String>> places = List.copyOf(told.keySet());
        List<Map<List<String>, FixtureTemplate>> out = new ArrayList<>();
        int alone = 0;
        for (List<String> place : places) {
            alone += told.get(place).size();
        }
        long together = places.size() < 2 ? 0 : 1;
        for (List<String> place : places) {
            if (places.size() > 1) {
                together = Math.min(together * told.get(place).size(), MOST_VALUES + 1L);
            }
        }
        if (alone + together > MOST_VALUES) {
            stopped.add(CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.figure());
        }
        for (List<String> place : places) {
            for (FixtureTemplate value : told.get(place)) {
                if (out.size() < MOST_VALUES) {
                    out.add(Map.of(place, value));
                }
            }
        }
        for (long at = 0; at < together && out.size() < MOST_VALUES; at++) {
            Map<List<String>, FixtureTemplate> placed = new LinkedHashMap<>();
            long rest = at;
            for (List<String> place : places) {
                List<FixtureTemplate> values = told.get(place);
                placed.put(place, values.get((int) (rest % values.size())));
                rest /= values.size();
            }
            out.add(placed);
        }
        return out;
    }

    /**
     * Every place inside the element, by the fields down to it, that {@code stated} says holds the
     * same value as a place outside the container — the place outside it, which a row holds a
     * value at.
     */
    private static void sameValuesIn(Proposition stated, TermPath element,
                                     Map<List<String>, TermPath> into) {
        switch (stated) {
            case Proposition.SameValue(DecisionSubject.AnInput(TermPath one, var _),
                                       DecisionSubject.AnInput(TermPath other, var _),
                                       boolean holds, var _) when holds -> {
                List<String> inOne = fieldsBelow(element, one);
                List<String> inOther = fieldsBelow(element, other);
                // Outside only where shown apart from the element as the value is reached: a
                // place narrowed to another reach of the element may be inside it on some row.
                if (inOne != null && inOther == null && !other.standsAtUnderOrAround(element)) {
                    into.putIfAbsent(inOne, other);
                } else if (inOther != null && inOne == null
                        && !one.standsAtUnderOrAround(element)) {
                    into.putIfAbsent(inOther, one);
                }
            }
            case Proposition.All all -> all.parts().forEach(each -> sameValuesIn(each, element,
                    into));
            case Proposition.Any any -> any.parts().forEach(each -> sameValuesIn(each, element,
                    into));
            case Proposition.Some some -> sameValuesIn(some.ofTheElement(), element, into);
            case Proposition.WhereItAnswers answers -> sameValuesIn(answers.states(), element,
                    into);
            default -> { }
        }
    }

    /** The fields from {@code element} down to {@code place} — none where it is the element
     *  itself — or null where it is not under it by fields alone. */
    private static List<String> fieldsBelow(TermPath element, TermPath place) {
        if (!place.isAtOrUnder(element)) {
            return null;
        }
        List<String> out = new ArrayList<>();
        for (TermPath.Step step : place.steps().subList(element.steps().size(),
                place.steps().size())) {
            if (!(step instanceof TermPath.Step.Field(String name))) {
                return null;
            }
            out.add(name);
        }
        return out;
    }

    /** {@code value} with {@code at}, a field and the fields of what is there, holding
     *  {@code put} — or null where it holds no such field. */
    private static ObservedValue withAt(ObservedValue value, List<String> at, ObservedValue put) {
        if (at.isEmpty()) {
            return put;
        }
        if (!(value instanceof ObservedValue.Constructed(var type, Map<String, ObservedValue> fields))
                || !fields.containsKey(at.getFirst())) {
            return null;
        }
        ObservedValue inner = withAt(fields.get(at.getFirst()), at.subList(1, at.size()), put);
        if (inner == null) {
            return null;
        }
        Map<String, ObservedValue> moved = new LinkedHashMap<>(fields);
        moved.put(at.getFirst(), inner);
        return new ObservedValue.Constructed(type, moved);
    }

    /** What the boundary builds of {@code element} as the one element of the container at
     *  parameter {@code at}, or null where it refuses it. */
    private static ObservedValue builtAlone(FixtureTemplate element, Container container,
                                            RowSearch.Building building) {
        return building.build(container.at(), container.holding(List.of(element)))
                .map(held -> container.inside(held)
                        instanceof ObservedValue.Sequence(List<ObservedValue> each)
                        && each.size() == container.filled(List.of(element)).size()
                        ? each.getFirst() : null)
                .orElse(null);
    }

    /**
     * The fewest elements the container is held with: one, or where the rules of its type ask
     * for more, that many. What a type asks is the count's own reading ({@link CountDomain}), so
     * it is asked of that and not found by building containers until the boundary takes one.
     */
    private static int fewestHeld(TermPath container, InputReading read) {
        NumericDomain.Bounds may = UndividedByARelation.howManyMayBeHeld(container, read,
                read.quantities().region());
        return may == null ? 1 : Math.max(1, CountDomain.leastFrom(may.min()));
    }

    /**
     * The container the elements are counted in, as a parameter of the behavior.
     *
     * @param at    which parameter it is
     * @param place where it stands
     * @param wrap  the container holding the elements it is handed, as a value of the type of the
     *              parameter, under the names that type wears
     * @param size  the fewest elements the boundary builds it with ({@link #fewestHeld})
     * @param overAgain whether it may hold an element over again
     */
    private record Container(int at, TermPath place,
                             Function<List<FixtureTemplate>, FixtureTemplate> wrap,
                             List<TypeSymbol> worn, int size, boolean overAgain) {

        /** What the boundary built of the container, with the names it wears taken off. */
        ObservedValue inside(ObservedValue built) {
            return ObservedValue.inside(worn, built);
        }

        /** {@code elements}, with the last of them over again up to the fewest the container is
         *  held with: the statement holds of the repeats as it does of that element. */
        List<FixtureTemplate> filled(List<FixtureTemplate> elements) {
            List<FixtureTemplate> out = new ArrayList<>(elements);
            while (out.size() < size) {
                out.add(elements.getLast());
            }
            return out;
        }

        /** The container holding {@link #filled} {@code elements}. */
        FixtureTemplate holding(List<FixtureTemplate> elements) {
            return wrap.apply(filled(elements));
        }
    }
}
