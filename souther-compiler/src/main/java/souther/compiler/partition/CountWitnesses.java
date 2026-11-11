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
import souther.compiler.observe.Figure;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Stream;

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
     * The row shown: every input, with the container holding the element the statement holds of
     * and then the one it fails of.
     *
     * @param inputs    the row, one fixture per parameter
     * @param container which parameter is the container
     * @param kept      the element the statement holds of
     * @param dropped   the element it fails of
     */
    public record Witness(List<FixtureTemplate> inputs, int container, FixtureTemplate kept,
                          FixtureTemplate dropped) {

        public Witness {
            inputs = List.copyOf(inputs);
        }
    }

    /**
     * A row at which {@code count}'s statement holds of one element and fails of another, the
     * behavior answering — or, where none was found, the figures the search stopped at first and
     * where the runs of the rows it tried stopped.
     *
     * <p>Only of a count of a parameter's own elements, of a container that may hold an element
     * over again: the rows a count is read over hold the witness's elements so many times each.
     *
     * @param named the values the model names at each parameter's type, tried before anything
     *              else is
     * @param taken what each row written for the behavior took, one value per parameter, as its
     *              run held it: tried next, each written back from what was built, and the
     *              elements of the container among them tried before what stands for the element
     */
    public static Sought of(Quantity.HowManyMeet count, String behavior, InputReading read,
                            List<List<FixtureTemplate>> named, List<List<ObservedValue>> taken,
                            RowSearch.Building building, RowSearch.Running running) {
        if (!(count.container() instanceof DecisionSubject.AnInput(TermPath container, var _))
                || !container.steps().isEmpty()
                || !read.domain().holdsAnElementOverAgain(container, read.rules())) {
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
        AStatementAtARow statement = AStatementAtARow.of(count.ofTheElement(), behavior,
                read.quantities());
        Set<Figure> stopped = new LinkedHashSet<>();
        Set<WhereARunStopped> runs = new LinkedHashSet<>();
        // What each parameter may hold, as far as the boundary builds it: the container as what
        // stands for a list of its element, which the elements tried below take the place of.
        // Every parameter is tried at all its values: what the statement counted turns on may name
        // a parameter the body does not read, and no one has said which are named.
        Set<String> readOutside = new LinkedHashSet<>();
        PositionsAStatementReads.of(count.ofTheElement()).orElse(List.of()).stream()
                .filter(place -> !place.head().equals(container.head()))
                .forEach(place -> readOutside.add(place.head()));
        List<List<RowSearch.Built>> each = RowSearch.tried(inputs.types(), named, taken,
                i -> i == at ? Type.list(element) : inputs.types().get(i), _ -> null,
                _ -> false, i -> readOutside.contains(inputs.parameters().get(i)), reading,
                building, stopped);
        if (each == null) {
            return new Sought(Optional.empty(), stopped, runs);
        }
        // And the elements the model writes in the container, each written back as a fixture of
        // the element's type, tried before what stands for that type.
        List<FixtureTemplate> written = new ArrayList<>();
        for (RowSearch.Built list : each.get(at)) {
            elementsOf(list.value(), element, reading, written, stopped);
        }
        each.set(at, each.get(at).subList(0, 1));
        // The rows of those, nearest first, as many as the search tries: one whose other values
        // leave no element to hold the statement of and another to fail it is no row shown that
        // none does, so the next is tried.
        for (List<RowSearch.Built> row : RowSearch.rowsOf(each, stopped)) {
            Optional<Witness> found = beside(row, at, element, container, count, inputs,
                    statement, reading, building, running, written, stopped, runs);
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
    private static Optional<Witness> beside(List<RowSearch.Built> beside, int at, Type element,
                                            TermPath container, Quantity.HowManyMeet count,
                                            BehaviorInputs inputs, AStatementAtARow statement,
                                            RuleReadingContext reading,
                                            RowSearch.Building building,
                                            RowSearch.Running running,
                                            List<FixtureTemplate> written,
                                            Set<Figure> stopped, Set<WhereARunStopped> runs) {
        List<FixtureTemplate> row = beside.stream().map(RowSearch.Built::fixture).toList();
        List<ObservedValue> built = beside.stream().map(RowSearch.Built::value).toList();
        FixtureTemplate kept = null;
        FixtureTemplate dropped = null;
        for (FixtureTemplate each : elementsTried(element, container, at, count.ofTheElement(),
                inputs, built, reading, building, written, stopped)) {
            Integer meet = metIn(List.of(each), at, built, inputs, statement, container,
                    building);
            if (meet == null) {
                continue;
            }
            if (meet == 1 && kept == null) {
                kept = each;
            } else if (meet == 0 && dropped == null) {
                dropped = each;
            }
            if (kept != null && dropped != null) {
                break;
            }
        }
        if (kept == null || dropped == null) {
            return Optional.empty();
        }
        List<FixtureTemplate> both = List.of(kept, dropped);
        Integer meet = metIn(both, at, built, inputs, statement, container, building);
        List<FixtureTemplate> shown = new ArrayList<>(row);
        shown.set(at, FixtureTemplate.collection(both));
        if (meet == null || meet != 1) {
            return Optional.empty();
        }
        RowSearch.Run ran = running.run(shown);
        if (!ran.getsThere()) {
            ran.stopped().ifPresent(runs::add);
            return Optional.empty();
        }
        return Optional.of(new Witness(shown, at, kept, dropped));
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
    private static Integer metIn(List<FixtureTemplate> elements, int at,
                                 List<ObservedValue> built, BehaviorInputs inputs,
                                 AStatementAtARow statement, TermPath container,
                                 RowSearch.Building building) {
        Optional<ObservedValue> held = building.build(at, FixtureTemplate.collection(elements));
        if (held.isEmpty()) {
            return null;
        }
        List<ObservedValue> values = new ArrayList<>(built);
        values.set(at, held.get());
        return counted(values, inputs, statement, container);
    }

    /**
     * The elements tried: those the model writes in the container ({@code inTheRows}), what stands
     * for the element's type, and each of the latter made to hold, at a place the statement says
     * is the same value as a place outside the container, every value the row holds there.
     */
    private static List<FixtureTemplate> elementsTried(Type element, TermPath container, int at,
                                                       Proposition stated, BehaviorInputs inputs,
                                                       List<ObservedValue> built,
                                                       RuleReadingContext reading,
                                                       RowSearch.Building building,
                                                       List<FixtureTemplate> inTheRows,
                                                       Set<Figure> stopped) {
        // In the order they are tried, and held to the figure once, over all of them: where they
        // come from decides which are tried first and never whether the figure applies.
        List<FixtureTemplate> standing = Partitions.representativesOf(element, reading).values();
        List<FixtureTemplate> out = new ArrayList<>(inTheRows);
        out.addAll(standing);
        Map<List<String>, TermPath> alike = new LinkedHashMap<>();
        sameValuesIn(stated, container.element(), alike);
        if (alike.isEmpty() || out.size() > MOST_VALUES) {
            return RowSearch.upTo(withWhatItReadsDiffering(out, element, container, stated,
                    reading), stopped);
        }
        BorderQuantity.Observation row = new StandingAtAPoint.DiscoveringRow(
                new StandingAtAPoint.RowWalk(inputs, new ObservedInputs(built,
                        new Generator.Watched.NotRun(), new AnswerObservation.NotAnswered())));
        making:
        for (FixtureTemplate base : standing) {
            ObservedValue each = builtAlone(base, at, building);
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
        return RowSearch.upTo(withWhatItReadsDiffering(out, element, container, stated, reading),
                stopped);
    }

    /**
     * {@code tried}, then the element with each place {@code stated} reads inside it at each of the
     * values its type tells apart, and everything else as the rules admit: the elements a
     * statement may tell apart by a place of their own, which the one value that stands for the
     * element does not. After what was tried, so that a row found without them is the row found.
     *
     * <p>A type that states a division — both of a {@code Bool}, each case of a sum — is taken at
     * every value that divides it, and any other at two values that differ
     * ({@link Witnesses#distinctValuesOf}): one a statement holds of and one it fails of is what
     * is looked for, and a type with no division of its own has no more than that to tell apart.
     * And at the values the statement itself names there ({@link ValuesAStatementNames}), which
     * are what it tells apart where the type tells nothing.
     *
     * <p>Each place alone first, then every place at once: a statement over two of them holds only
     * where both are at the values it asks for. The ways the places can be together are counted as
     * far as the figure the elements are tried to ({@link RowSearch#upTo}), which is said where
     * they come to more.
     */
    private static List<FixtureTemplate> withWhatItReadsDiffering(
            List<FixtureTemplate> tried, Type element, TermPath container, Proposition stated,
            RuleReadingContext reading) {
        RuleReadingSource source = reading.source();
        Map<TermPath, List<Object>> named = ValuesAStatementNames.of(stated);
        Map<List<String>, List<FixtureTemplate>> told = new LinkedHashMap<>();
        for (TermPath place : PositionsAStatementReads.of(stated).orElse(List.of())) {
            List<String> fields = fieldsBelow(container.element(), place);
            Type type = fields == null ? null : Witnesses.typeAt(element, fields, reading);
            if (type == null) {
                continue;
            }
            int divided = Distinctions.ofType(TypeView.shapeOf(type, source.inners(),
                    source.symbols(), source.kinds(), source.sums()), source.symbols(),
                    source.kinds(), source.sums()).size();
            List<FixtureTemplate> values = new ArrayList<>(Witnesses.distinctValuesOf(type,
                    Math.max(2, divided), reading, Set.of()).values());
            for (Object constant : named.getOrDefault(place, List.of())) {
                FixtureTemplate written = Witnesses.writtenAs(constant, type, reading);
                if (written != null && !values.contains(written)) {
                    values.add(written);
                }
            }
            if (!values.isEmpty()) {
                told.putIfAbsent(fields, values);
            }
        }
        List<FixtureTemplate> out = new ArrayList<>(tried);
        List<Map<List<String>, FixtureTemplate>> together = List.of(Map.of());
        for (Map.Entry<List<String>, List<FixtureTemplate>> place : told.entrySet()) {
            List<Map<List<String>, FixtureTemplate>> next = new ArrayList<>();
            for (Map<List<String>, FixtureTemplate> so : together) {
                for (FixtureTemplate value : place.getValue()) {
                    Map<List<String>, FixtureTemplate> more = new LinkedHashMap<>(so);
                    more.put(place.getKey(), value);
                    next.add(more);
                }
            }
            // Past the figure, one more is as much as is needed to say it is passed.
            together = next.size() > MOST_VALUES ? next.subList(0, MOST_VALUES + 1) : next;
        }
        List<Map<List<String>, FixtureTemplate>> alone = new ArrayList<>();
        told.forEach((fields, values) -> values.forEach(value -> alone.add(Map.of(fields, value))));
        for (Map<List<String>, FixtureTemplate> placed : Stream.concat(alone.stream(),
                together.stream()).toList()) {
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

    /** The fields from {@code element} down to {@code place}, or null where it is not under it
     *  by fields alone. */
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
        return out.isEmpty() ? null : out;
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
    private static ObservedValue builtAlone(FixtureTemplate element, int at,
                                            RowSearch.Building building) {
        return building.build(at, FixtureTemplate.collection(List.of(element)))
                .map(held -> held instanceof ObservedValue.Sequence(List<ObservedValue> each)
                        && each.size() == 1 ? each.getFirst() : null)
                .orElse(null);
    }
}
