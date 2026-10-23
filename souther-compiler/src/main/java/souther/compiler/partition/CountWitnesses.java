package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * A row of a behavior's inputs at which a counted statement holds of one element of the container
 * and fails of another, beside one and the same value of everything else the behavior takes — and
 * at which the behavior answers, the run going through the comparison it is asked for.
 *
 * <p>Found and then shown. Which values are tried is a search, and a search may miss: a named value
 * of a parameter's type the model writes ({@code TypedFixtureValues}), what stands for each type
 * ({@link Partitions#representativesOf}), and an element made to hold, at the place a statement
 * says is the same value as a place outside the container, each value the row holds there. None of
 * that is a claim. What is a claim is what the boundary built of the row ({@link Building}), what
 * the statement says of each element of what it built ({@link AStatementAtARow#howManyMeetIn}) —
 * one element it holds of and one it fails of, and none it could not tell — and that the behavior
 * answered on it, a run of it going through the comparison ({@link Running}). A row the search did
 * not find is no row shown not to exist.
 *
 * <p>A witness is of one comparison as well as of one count: the way to a comparison may ask
 * something of what the row holds beside the container, and a row that meets the statement both
 * ways and answers somewhere else shows nothing of that comparison. What the reading of the
 * comparison makes of the witness — every count of every size — is that reading's
 * ({@code UndividedByARelation}).
 */
public final class CountWitnesses {

    /** How many of a parameter's values are tried before the search stops. */
    private static final int MOST_VALUES =
            CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.maximum();

    private CountWitnesses() {}

    /**
     * Where the reading of one comparison asks for a witness of a count it reads ({@link #of}):
     * one whose row gets to that comparison.
     *
     * <p>Handed to a reading and not kept in what it reads: a witness is found by running what
     * the compile produced, which the reading of an input is not made of.
     */
    public interface Lookup {

        /** What the search for a witness of {@code count} whose row gets to the comparison being
         *  read came to. */
        Sought of(Quantity.HowManyMeet count);

        /** Nothing found for any count: nothing more is shown than the reading shows alone. */
        Lookup NONE = _ -> Sought.NOTHING;
    }

    /**
     * What a search for a witness came to: the witness, where one was found, and where none was,
     * the figures the search stopped at before it had tried everything it would have.
     *
     * <p>Two misses apart. A search that tried all it had and found nothing, and one that stopped
     * at a figure, both leave the count not shown; a run allowed more may find a witness in the
     * second and never in the first, and the figure is what says which a reader has.
     *
     * @param found     the witness, or empty
     * @param stoppedAt the figures the search stopped at, none where one was found
     */
    public record Sought(Optional<Witness> found, Set<CompositionBudget> stoppedAt) {

        /** Nothing tried and nothing stopped at. */
        public static final Sought NOTHING = new Sought(Optional.empty(), Set.of());

        public Sought {
            stoppedAt = found.isPresent() ? Set.of() : Set.copyOf(stoppedAt);
        }
    }

    /** Where the reading of a body asks for the witnesses of the comparison it reads, by which
     *  comparison of the body it is. */
    public interface AtComparisons {

        /** Where the reading of {@code comparison} asks for a witness of a count it reads. */
        Lookup at(ConstructOccurrence comparison);

        /** Nothing found for any comparison. */
        AtComparisons NONE = _ -> Lookup.NONE;
    }

    /** What the boundary builds of one input at a parameter, or empty where it refuses it. */
    public interface Building {
        Optional<ObservedValue> build(int parameter, FixtureTemplate fixture);
    }

    /** Whether the behavior answers on a row of these inputs, a run of it going through the
     *  comparison the witness is asked for. */
    public interface Running {
        boolean getsThere(List<FixtureTemplate> inputs);
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
     * behavior answering — or, where none was found, the figures the search stopped at first.
     *
     * <p>Only of a count of a parameter's own elements: the container is a list a parameter is.
     *
     * @param named the values the model names at each parameter's type, tried before anything
     *              else is
     */
    public static Sought of(Quantity.HowManyMeet count, String behavior, InputReading read,
                            List<List<FixtureTemplate>> named, Building building,
                            Running running) {
        if (!(count.container() instanceof DecisionSubject.AnInput(TermPath container))
                || !container.steps().isEmpty()
                || !read.domain().holdsItsElementsInTheOrderWritten(container, read.rules())) {
            return Sought.NOTHING;
        }
        BehaviorInputs inputs = BehaviorInputs.of(read);
        int at = inputs.parameters().indexOf(container.head());
        Type element = read.domain().typeAt(container.element(), read.rules());
        if (at < 0 || element == null) {
            return Sought.NOTHING;
        }
        RuleReadingContext reading = RuleReadingContext.of(read.rules(), read.domain().policy(),
                read.domain().machines());
        AStatementAtARow statement = AStatementAtARow.of(count.ofTheElement(), behavior,
                read.quantities());
        Set<CompositionBudget> stopped = EnumSet.noneOf(CompositionBudget.class);
        // What each parameter may hold, as far as the boundary builds it: the container as what
        // stands for a list of its element, which the elements tried below take the place of.
        List<List<Built>> each = new ArrayList<>();
        for (int i = 0; i < inputs.parameters().size(); i++) {
            List<FixtureTemplate> tried = new ArrayList<>(named.get(i));
            tried.addAll(Partitions.representativesOf(i == at ? Type.list(element)
                    : inputs.types().get(i), reading).values());
            List<Built> made = new ArrayList<>();
            for (FixtureTemplate one : upTo(tried, stopped)) {
                building.build(i, one).ifPresent(value -> made.add(new Built(one, value)));
            }
            if (made.isEmpty()) {
                return new Sought(Optional.empty(), stopped);
            }
            each.add(i == at ? made.subList(0, 1) : made);
        }
        // The rows of those, nearest first, as many as the search tries: one whose other values
        // leave no element to hold the statement of and another to fail it is no row shown that
        // none does, so the next is tried.
        for (List<Built> row : rowsOf(each, stopped)) {
            Optional<Witness> found = beside(row, at, element, container, count, inputs,
                    statement, reading, building, running, stopped);
            if (found.isPresent()) {
                return new Sought(found, Set.of());
            }
        }
        return new Sought(Optional.empty(), stopped);
    }

    /** As many of {@code values} as the search tries, first first, with the figure added to
     *  {@code stopped} where some are left untried. */
    private static <T> List<T> upTo(List<T> values, Set<CompositionBudget> stopped) {
        if (values.size() <= MOST_VALUES) {
            return values;
        }
        stopped.add(CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG);
        return values.subList(0, MOST_VALUES);
    }

    /** One input the boundary built, and the fixture it was built of. */
    private record Built(FixtureTemplate fixture, ObservedValue value) {}

    /** Rows taking one value of each parameter, nearest first — every parameter at its first
     *  before any at its second — and no more than the search tries, with the figure added to
     *  {@code stopped} where some are left untried. */
    private static List<List<Built>> rowsOf(List<List<Built>> each,
                                            Set<CompositionBudget> stopped) {
        List<List<Built>> out = new ArrayList<>();
        int[] at = new int[each.size()];
        while (true) {
            if (out.size() == MOST_VALUES) {
                stopped.add(CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG);
                break;
            }
            List<Built> row = new ArrayList<>();
            for (int i = 0; i < each.size(); i++) {
                row.add(each.get(i).get(at[i]));
            }
            out.add(row);
            int moved = 0;
            while (moved < at.length && at[moved] + 1 >= each.get(moved).size()) {
                at[moved] = 0;
                moved++;
            }
            if (moved == at.length) {
                break;
            }
            at[moved]++;
        }
        return out;
    }

    /** A witness whose other inputs are {@code beside}'s, or empty where none was found there. */
    private static Optional<Witness> beside(List<Built> beside, int at, Type element,
                                            TermPath container, Quantity.HowManyMeet count,
                                            BehaviorInputs inputs, AStatementAtARow statement,
                                            RuleReadingContext reading, Building building,
                                            Running running, Set<CompositionBudget> stopped) {
        List<FixtureTemplate> row = beside.stream().map(Built::fixture).toList();
        List<ObservedValue> built = beside.stream().map(Built::value).toList();
        FixtureTemplate kept = null;
        FixtureTemplate dropped = null;
        for (FixtureTemplate each : elementsTried(element, container, at, count.ofTheElement(),
                inputs, built, reading, building, stopped)) {
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
        if (meet == null || meet != 1 || !running.getsThere(shown)) {
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
                                          Building building) {
        if (!(count.container() instanceof DecisionSubject.AnInput(TermPath container))
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
                                 Building building) {
        Optional<ObservedValue> held = building.build(at, FixtureTemplate.collection(elements));
        if (held.isEmpty()) {
            return null;
        }
        List<ObservedValue> values = new ArrayList<>(built);
        values.set(at, held.get());
        return counted(values, inputs, statement, container);
    }

    /**
     * The elements tried: what stands for the element's type, and each of those made to hold, at
     * a place the statement says is the same value as a place outside the container, every value
     * the row holds there.
     */
    private static List<FixtureTemplate> elementsTried(Type element, TermPath container, int at,
                                                       Proposition stated, BehaviorInputs inputs,
                                                       List<ObservedValue> built,
                                                       RuleReadingContext reading,
                                                       Building building,
                                                       Set<CompositionBudget> stopped) {
        List<FixtureTemplate> standing = Partitions.representativesOf(element, reading).values();
        List<FixtureTemplate> out = new ArrayList<>(standing);
        Map<List<String>, TermPath> alike = new LinkedHashMap<>();
        sameValuesIn(stated, container.element(), alike);
        if (alike.isEmpty()) {
            return out;
        }
        BorderQuantity.Observation row = new StandingAtAPoint.DiscoveringRow(
                new StandingAtAPoint.RowWalk(inputs, new ObservedInputs(built,
                        new Generator.Watched.NotRun(), new AnswerObservation.NotAnswered())));
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
                for (ObservedValue value : upTo(there, stopped)) {
                    ObservedValue moved = withAt(each, place.getKey(), value);
                    if (moved != null && ObservedFixtures.of(moved, element, reading)
                            instanceof ObservedFixtures.Writing.Written<FixtureTemplate>(
                                    FixtureTemplate written)) {
                        out.add(written);
                    }
                }
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
            case Proposition.SameValue(DecisionSubject.AnInput(TermPath one),
                                       DecisionSubject.AnInput(TermPath other), boolean holds,
                                       var _) when holds -> {
                List<String> inOne = fieldsBelow(element, one);
                List<String> inOther = fieldsBelow(element, other);
                if (inOne != null && inOther == null && !other.isAtOrUnder(element)) {
                    into.putIfAbsent(inOne, other);
                } else if (inOther != null && inOne == null && !one.isAtOrUnder(element)) {
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
    private static ObservedValue builtAlone(FixtureTemplate element, int at, Building building) {
        return building.build(at, FixtureTemplate.collection(List.of(element)))
                .map(held -> held instanceof ObservedValue.Sequence(List<ObservedValue> each)
                        && each.size() == 1 ? each.getFirst() : null)
                .orElse(null);
    }
}
