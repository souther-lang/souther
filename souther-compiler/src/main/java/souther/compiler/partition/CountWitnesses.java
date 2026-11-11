package souther.compiler.partition;

import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.Distinctions;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.PositionsAStatementReads;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.numeric.CountDomain;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.observe.Figure;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.values.Operand;
import souther.compiler.values.Value;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

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
     * @param expansion how far the two elements the row holds say the count goes: to every value up
     *                  to the size of the container, or to no more than the two
     */
    public record Witness(List<FixtureTemplate> inputs, int container, FixtureTemplate one,
                          FixtureTemplate other, FixtureTemplate failing, Expansion expansion) {

        public Witness {
            inputs = List.copyOf(inputs);
        }

        /** Whether the count is shown at every value from none up to the size of the container. */
        public boolean takesEverySize() {
            return expansion != Expansion.ONLY_THESE;
        }
    }

    /**
     * What a row that holds one element the statement holds of and another it fails of shows of
     * the counts beside them. It is the type's and the statement's, and no rule's: a rule that
     * keeps elements apart leaves a container fewer to hold, which is what
     * {@code UndividedByARelation#howManyAreHeld} says of it, and a count is shown only as far as
     * that.
     */
    public enum Expansion {
        /** A list may hold an element over again, so a row holds the one the statement holds of
         *  as many times as it likes. */
        REPEATED_ELEMENT,
        /** A map holds an entry under each key, and the statement reads no key: the entries it
         *  holds of and those it fails of may be put under as many different keys as the map may
         *  hold, each of them any number of times. */
        INDEPENDENT_KEYS,
        /** The two elements and no more: a set holds each element once, and a statement that reads
         *  the key of an entry says of another key what it has no reason to say of the first. */
        ONLY_THESE
    }

    /**
     * A row at which {@code count}'s statement holds of one element and fails of another, the
     * behavior answering — or, for a count of different values, a row whose container holds two
     * elements the statement keeps that hold different values — or, where none was found, the
     * figures the search stopped at first and where the runs of the rows it tried stopped.
     *
     * <p>Only of a count of a parameter's own elements, of a list, a set or a map. Where it is a list
     * the rows a count is read over hold the witness's elements so many times each; a set holds each
     * once, and what the witness shows of it is the one element and the other. A map's element is an
     * entry, a key and a value built together and held under a key once ({@link Witness#expansion}).
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
        // A map holds an entry, which is a key and a value: counted of the entries that meet a
        // statement, and no further than that.
        boolean ofEntries = read.domain().entryOf(container, read.rules()).size() == 2;
        if (ofEntries ? asked.differentAt().isPresent()
                : !repeats && !read.domain().holdsEachElementOnce(container, read.rules())) {
            return Sought.NOTHING;
        }
        BehaviorInputs inputs = BehaviorInputs.of(read);
        int at = inputs.parameters().indexOf(container.head());
        Type element = read.domain().typeAt(container.element(), read.rules());
        Type key = ofEntries ? read.domain().typeAt(container.key(), read.rules()) : null;
        if (at < 0 || element == null || (ofEntries && key == null)) {
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
        List<FixtureTemplate> writtenKeys = new ArrayList<>();
        for (RowSearch.Built list : each.get(at)) {
            ObservedValue held = ObservedValue.inside(worn, list.value());
            if (ofEntries) {
                entriesOf(held, key, element, reading, writtenKeys, written, stopped);
            } else {
                elementsOf(held, element, reading, written, stopped);
            }
        }
        int fewest = repeats || ofEntries ? fewestHeld(container, read) : 1;
        List<FixtureTemplate> keyPool = !ofEntries ? List.of()
                : keysToFillWith(key, fewest, reading, stopped);
        Container holder = new Container(at, container, spelled::holding, worn, fewest, repeats,
                key, writtenKeys, new Entries(), keyPool, place -> mayHold(place, read));
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

    /**
     * Keys that differ, to put the fewest entries a map is held with under, and a pair to spare:
     * the keys are what keeps its entries apart. No more are asked for than the search tries, and
     * where the fewest is more than that the figure is added to {@code stopped}.
     */
    private static List<FixtureTemplate> keysToFillWith(Type key, int fewest,
                                                        RuleReadingContext reading,
                                                        Set<Figure> stopped) {
        int asked = Math.min(fewest + 2, MOST_VALUES + 1);
        if (fewest + 2 > asked) {
            stopped.add(CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.figure());
        }
        return List.copyOf(Witnesses.distinctValuesOf(key, asked, reading, Set.of()).values());
    }

    /** Adds to {@code keys} and to {@code values} the key and the value of each entry of
     *  {@code map}, a map the boundary built, each written back as a fixture of its type and each
     *  once — and to {@code stopped} the figure it was cut short at, where it was. */
    private static void entriesOf(ObservedValue map, Type key, Type value,
                                  RuleReadingContext reading, List<FixtureTemplate> keys,
                                  List<FixtureTemplate> values, Set<Figure> stopped) {
        if (map instanceof ObservedValue.Truncated(Figure cut)) {
            stopped.add(cut);
        }
        if (!(map instanceof ObservedValue.Mapping(List<ObservedValue.Entry> held))) {
            return;
        }
        for (ObservedValue.Entry each : held) {
            if (ObservedFixtures.of(each.key(), key, reading)
                    instanceof ObservedFixtures.Writing.Written<FixtureTemplate>(
                            FixtureTemplate written)
                    && !keys.contains(written)) {
                keys.add(written);
            }
            if (ObservedFixtures.of(each.value(), value, reading)
                    instanceof ObservedFixtures.Writing.Written<FixtureTemplate>(
                            FixtureTemplate written)
                    && !values.contains(written)) {
                values.add(written);
            }
        }
    }

    /**
     * The entries tried of a map: each key tried with each value tried, the pairs nearest the
     * first of each first, as many as the search tries — with the figure said in {@code stopped}
     * where there are more.
     */
    private static List<FixtureTemplate> entriesTried(List<FixtureTemplate> keys,
                                                      List<FixtureTemplate> values,
                                                      Container held, Set<Figure> stopped) {
        List<FixtureTemplate> out = new ArrayList<>();
        int farthest = keys.size() + values.size() - 2;
        for (int sum = 0; sum <= farthest; sum++) {
            for (int value = Math.max(0, sum - keys.size() + 1);
                    value <= Math.min(sum, values.size() - 1); value++) {
                if (out.size() >= MOST_VALUES) {
                    stopped.add(CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.figure());
                    return out;
                }
                out.add(held.entries().of(keys.get(sum - value), values.get(value)));
            }
        }
        return out;
    }

    /** Whether the statement reads the key of an entry, or reads something that is no place. */
    private static boolean readsAKey(Asked asked, TermPath container) {
        return asked.reads().map(read -> read.stream().anyMatch(place ->
                place.isAtOrUnder(container.key()))).orElse(true);
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
        Slot valueSlot = new Slot(container.place().element(), element, false);
        List<FixtureTemplate> tried;
        if (container.key() == null) {
            tried = elementsTried(valueSlot, null, container, asked, inputs, built, reading,
                    building, written, stopped);
        } else {
            Slot keySlot = new Slot(container.place().key(), container.key(), true);
            // Each is tried beside one that stands for the other: an entry is both.
            List<FixtureTemplate> aKey = Partitions.representativesOf(container.key(), reading)
                    .values();
            List<FixtureTemplate> aValue = Partitions.representativesOf(element, reading)
                    .values();
            if (aKey.isEmpty() || aValue.isEmpty()) {
                return Optional.empty();
            }
            List<FixtureTemplate> values = elementsTried(valueSlot, aKey.getFirst(), container,
                    asked, inputs, built, reading, building, written, stopped);
            List<FixtureTemplate> keys = elementsTried(keySlot, aValue.getFirst(), container,
                    asked, inputs, built, reading, building, container.writtenKeys(), stopped);
            tried = entriesTried(keys, values, container, stopped);
        }
        boolean ofValues = asked.differentAt().isPresent();
        // A pair is a witness only once the container holds it, the statement tells it apart as
        // the count asks, and a run of the row it makes gets to the comparison: the three are one
        // question of one pair, so a pair that fails the last is no reason to look at no other.
        Predicate<List<FixtureTemplate>> getsThere = pair -> {
            RowSearch.Run ran = running.run(rowHolding(row, container, pair));
            if (!ran.getsThere()) {
                ran.stopped().ifPresent(runs::add);
            }
            return ran.getsThere();
        };
        List<FixtureTemplate> both = ofValues
                ? twoThatDiffer(tried, container, asked.differentAt().get(), built, inputs,
                        statement, building, getsThere, stopped)
                : oneKeptAndOneDropped(tried, container, built, inputs, statement, building,
                        reading, getsThere, stopped);
        if (both == null) {
            return Optional.empty();
        }
        // What fails the statement is the second of a count of elements; of a count of values it is
        // one more element, which none is where every element meets the statement.
        FixtureTemplate failing = ofValues
                ? aFailingElement(tried, container, built, inputs, statement, building)
                : both.getLast();
        Expansion expansion = container.overAgain() ? Expansion.REPEATED_ELEMENT
                : container.key() != null && !readsAKey(asked, container.place())
                ? Expansion.INDEPENDENT_KEYS : Expansion.ONLY_THESE;
        return Optional.of(new Witness(rowHolding(row, container, both), container.at(),
                both.getFirst(), both.getLast(), failing, expansion));
    }

    /** {@code row} with the container holding {@code elements}. */
    private static List<FixtureTemplate> rowHolding(List<FixtureTemplate> row, Container container,
                                                    List<FixtureTemplate> elements) {
        List<FixtureTemplate> shown = new ArrayList<>(row);
        shown.set(container.at(), container.holding(elements));
        return shown;
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
                                                              RowSearch.Building building,
                                                              RuleReadingContext reading,
                                                              Predicate<List<FixtureTemplate>>
                                                                      getsThere,
                                                              Set<Figure> stopped) {
        List<FixtureTemplate> kept = new ArrayList<>();
        List<FixtureTemplate> dropped = new ArrayList<>();
        for (FixtureTemplate each : tried) {
            if (container.key() != null) {
                // The entries a map is filled with are under other keys, and what the statement
                // says of them is its own to say: it is asked of the entry, not of the count.
                Boolean holds = entryHolds(each, container, built, inputs, statement, building,
                        reading);
                if (holds != null) {
                    (holds ? kept : dropped).add(each);
                }
                continue;
            }
            Integer meet = metIn(List.of(each), container, built, inputs, statement, building);
            if (meet == null) {
                continue;
            }
            // The container holds the element over again where a rule asks for more than one, so
            // it holds the statement of all of them or of none.
            if (meet == container.filled(List.of(each)).size()) {
                kept.add(each);
            } else if (meet == 0) {
                dropped.add(each);
            }
        }
        return firstPairThat(kept, dropped, false, pair -> {
            Integer meet = metIn(pair, container, built, inputs, statement, building);
            return meet != null && meet == 1 && getsThere.test(pair);
        }, stopped);
    }

    /**
     * Whether the statement holds of {@code entry}, in the container the boundary builds of it
     * filled to the fewest it is held with — or null where the boundary refused the container or
     * kept fewer entries than it was given, or the statement could not tell of the entry.
     */
    private static Boolean entryHolds(FixtureTemplate entry, Container container,
                                      List<ObservedValue> built, BehaviorInputs inputs,
                                      AStatementAtARow statement, RowSearch.Building building,
                                      RuleReadingContext reading) {
        Optional<ObservedValue> held = building.build(container.at(),
                container.holding(List.of(entry)));
        if (held.isEmpty()
                || !(container.inside(held.get()) instanceof ObservedValue.Mapping(var entries)
                        && entries.size() == container.filled(List.of(entry)).size())) {
            return null;
        }
        List<ObservedValue> values = new ArrayList<>(built);
        values.set(container.at(), held.get());
        List<AStatementAtARow.OfAnElement> answers = statement.eachIn(container.place(),
                new StandingAtAPoint.DiscoveringRow(new StandingAtAPoint.RowWalk(inputs,
                        new ObservedInputs(values, new Generator.Watched.NotRun(),
                                new AnswerObservation.NotAnswered()))));
        if (answers == null) {
            return null;
        }
        for (AStatementAtARow.OfAnElement each : answers) {
            if (each.key() != null && ObservedFixtures.of(each.key(), container.key(), reading)
                    instanceof ObservedFixtures.Writing.Written<FixtureTemplate>(
                            FixtureTemplate key)
                    && key.equals(container.entries().keyOf(entry))) {
                return switch (each.answer()) {
                    case AStatementAtARow.Answer.Holds _ -> Boolean.TRUE;
                    case AStatementAtARow.Answer.Fails _ -> Boolean.FALSE;
                    case AStatementAtARow.Answer.CouldNotTell _ -> null;
                };
            }
        }
        return null;
    }

    /**
     * The first pair of an element of {@code ones} and one of {@code others} — two of {@code ones}
     * where {@code ofOne}, the earlier first — that {@code holds} of, in the order the elements were
     * tried, or null where none does.
     *
     * <p>A pair is a witness only where everything that is asked of it holds of it together: that
     * the container holds the two, that they are what the count tells apart, that a run of the row
     * they make gets to the comparison. What the container asks of the elements it holds together
     * is its own, and a run is of the row and not of each, so the whole of it is the one question
     * {@code holds} answers, and a pair that fails any part is no reason to look at no other. Held
     * to the figure the elements are tried to; where the figure stops the asking it is said, and
     * nothing is shown that the pairs left unasked would.
     */
    static <T> List<T> firstPairThat(List<T> ones, List<T> others, boolean ofOne,
                                     Predicate<List<T>> holds, Set<Figure> stopped) {
        int asked = 0;
        for (int one = 0; one < ones.size(); one++) {
            for (int other = ofOne ? one + 1 : 0; other < (ofOne ? ones : others).size();
                    other++) {
                if (asked++ >= MOST_VALUES) {
                    stopped.add(CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.figure());
                    return null;
                }
                List<T> pair = List.of(ones.get(one), (ofOne ? ones : others).get(other));
                if (holds.test(pair)) {
                    return pair;
                }
            }
        }
        return null;
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
                                                       RowSearch.Building building,
                                                       Predicate<List<FixtureTemplate>> getsThere,
                                                       Set<Figure> stopped) {
        List<FixtureTemplate> kept = new ArrayList<>();
        for (FixtureTemplate each : tried) {
            Integer meet = metIn(List.of(each), container, built, inputs, statement, building);
            if (meet != null && meet == container.filled(List.of(each)).size()) {
                kept.add(each);
            }
        }
        return firstPairThat(kept, kept, true, pair -> {
            Integer different = differentIn(pair, container, at, built, inputs, statement,
                    building);
            return different != null && different == 2 && getsThere.test(pair);
        }, stopped);
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
    public static Optional<Integer> metOn(Quantity.CountedOverAContainer counted, String behavior,
                                          InputReading read, List<FixtureTemplate> inputs,
                                          RowSearch.Building building) {
        if (!(counted instanceof Quantity.HowManyMeet count)
                || !(count.container() instanceof DecisionSubject.AnInput(TermPath container,
                        var _))
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
     * could not tell of some element. A map the boundary built with fewer entries than it was
     * given, two filed under one key and kept as one, is refused: the elements are not what it
     * holds.
     */
    private static Integer metIn(List<FixtureTemplate> elements, Container container,
                                 List<ObservedValue> built, BehaviorInputs inputs,
                                 AStatementAtARow statement, RowSearch.Building building) {
        Optional<ObservedValue> held = building.build(container.at(),
                container.holding(elements));
        if (held.isEmpty() || (container.key() != null
                && !(container.inside(held.get()) instanceof ObservedValue.Mapping(var entries)
                        && entries.size() == container.filled(elements).size()))) {
            return null;
        }
        List<ObservedValue> values = new ArrayList<>(built);
        values.set(container.at(), held.get());
        return counted(values, inputs, statement, container.place());
    }

    /**
     * The values tried at {@code slot}, an element of the container or the key of an entry: those
     * the model writes in the container ({@code inTheRows}), what stands for the type there, and
     * each of the latter made to hold, at a place the statement says is the same value as a place
     * outside the container, every value the row holds there.
     *
     * <p>The slot is where the statement is asked of, and the one question is the same of a value
     * and of a key: what the statement reads inside it, and what it says is the same as a value the
     * row holds beside the container. {@code partner} is what stands for the other half of an
     * entry, which the boundary needs to build the entry the value is read back from.
     */
    private static List<FixtureTemplate> elementsTried(Slot slot, FixtureTemplate partner,
                                                       Container held, Asked asked,
                                                       BehaviorInputs inputs,
                                                       List<ObservedValue> built,
                                                       RuleReadingContext reading,
                                                       RowSearch.Building building,
                                                       List<FixtureTemplate> inTheRows,
                                                       Set<Figure> stopped) {
        Type element = slot.type();
        Proposition stated = asked.statement();
        // In the order they are tried, and held to the figure once, over all of them: where they
        // come from decides which are tried first and never whether the figure applies. Two keys
        // that differ are what an entry needs of its key, and a value is one that stands for it.
        List<FixtureTemplate> standing = slot.ofKey()
                ? new ArrayList<>(Witnesses.distinctValuesOf(element, valuesAskedOfAType(2),
                        reading, Set.of()).values())
                : Partitions.representativesOf(element, reading).values();
        List<FixtureTemplate> out = new ArrayList<>(inTheRows);
        if (slot.ofKey()) {
            standing.stream().filter(each -> !out.contains(each)).forEach(out::add);
        } else {
            out.addAll(standing);
        }
        Map<List<String>, TermPath> alike = new LinkedHashMap<>();
        sameValuesIn(stated, slot.root(), alike);
        if (out.size() > MOST_VALUES) {
            return RowSearch.upTo(out, stopped);
        }
        if (alike.isEmpty()) {
            return RowSearch.upTo(withWhatItReadsDiffering(out, element, slot.root(), held, asked,
                    reading, stopped), stopped);
        }
        BorderQuantity.Observation row = new StandingAtAPoint.DiscoveringRow(
                new StandingAtAPoint.RowWalk(inputs, new ObservedInputs(built,
                        new Generator.Watched.NotRun(), new AnswerObservation.NotAnswered())));
        making:
        for (FixtureTemplate base : standing) {
            ObservedValue each = builtAlone(base, slot, partner, held, reading, building);
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
        return RowSearch.upTo(withWhatItReadsDiffering(out, element, slot.root(), held, asked,
                reading, stopped), stopped);
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
            List<FixtureTemplate> tried, Type element, TermPath root, Container held,
            Asked asked, RuleReadingContext reading, Set<Figure> stopped) {
        RuleReadingSource source = reading.source();
        Map<TermPath, List<ValuesAStatementNames.Named>> named =
                ValuesAStatementNames.of(asked.statement());
        Map<List<String>, List<FixtureTemplate>> told = new LinkedHashMap<>();
        for (TermPath place : asked.reads().orElse(List.of())) {
            // The keys of a map the element holds, and the elements of a list or a set it holds,
            // are told apart by the collection: one holding the value the statement names there,
            // and one holding none, beside what the collection's own type tells apart.
            TermPath collection = place.mapOfTheKeys() != null ? place.mapOfTheKeys()
                    : !place.steps().isEmpty()
                    && place.steps().getLast() instanceof TermPath.Step.Element
                    ? place.prefix(place.steps().size() - 1) : null;
            List<String> fieldsToIt =
                    collection == null ? null : fieldsBelow(root, collection);
            // A collection is one inside what is tried at the root. The keys of the container
            // being counted, and its elements, are no such collection: a place that is the root
            // itself is read as the place it is, below.
            if (fieldsToIt != null) {
                List<FixtureTemplate> collections = collectionsTold(
                        Witnesses.typeAt(element, fieldsToIt, reading),
                        place.mapOfTheKeys() != null,
                        named.getOrDefault(place, List.of()),
                        named.getOrDefault(collection, List.of()),
                        held.mayHold().apply(collection), reading, stopped);
                if (!collections.isEmpty()) {
                    List<FixtureTemplate> both =
                            new ArrayList<>(told.getOrDefault(fieldsToIt, List.of()));
                    collections.stream().filter(each -> !both.contains(each)).forEach(both::add);
                    told.put(fieldsToIt, RowSearch.upTo(both, stopped));
                }
                continue;
            }
            List<String> fields = fieldsBelow(root, place);
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
                    case ValuesAStatementNames.Named.AtValue(Value value) ->
                            Witnesses.writtenAs(value, type, reading);
                    case ValuesAStatementNames.Named.Holding(BigInteger many) ->
                            Witnesses.holdingMany(type, many, reading);
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
     * The collections of {@code type} that tell apart what a statement names as their keys, where
     * {@code ofTheKeys}, or as their elements: one holding none of the values named, and one
     * holding each way of some of them — a map filing each under a value its entries are written
     * with — or none where {@code type} is not such a collection. A value named that is not
     * written at the type the collection holds is left out.
     *
     * <p>A statement may also say how many the collection holds ({@code sizes}, which
     * {@link ValuesAStatementNames.Named.Holding} names at the collection's own place), and the
     * one collection has to meet both: each way of holding some of the values is also made
     * holding that many.
     *
     * <p>Each is asked of the collection's own builder ({@link Witnesses#holding}), with the
     * values named and not chosen kept out of it: what may stand beside the ones chosen — a list
     * may say the same value again and a set may not, a map's keys are apart, and a floor the
     * rules give — is the carrier's and the rules' to say, as it is for a plan composed into a
     * row. What that build met of this compiler's figures is said in {@code stopped}.
     */
    private static List<FixtureTemplate> collectionsTold(
            Type type, boolean ofTheKeys, List<ValuesAStatementNames.Named> names,
            List<ValuesAStatementNames.Named> sizes, DeclaredBounds.CountRange rules,
            RuleReadingContext reading, Set<Figure> stopped) {
        if (type == null || names.isEmpty()) {
            return List.of();
        }
        RuleReadingSource source = reading.source();
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        Type held = switch (view.shape()) {
            case Shape.Mapping mapping when ofTheKeys -> mapping.key();
            case Shape.Sequence sequence when !ofTheKeys -> sequence.element();
            default -> null;
        };
        if (held == null) {
            return List.of();
        }
        // Each value named is a membership the collection has or has not, independent of the
        // others: a statement over several holds of the collections that have some of them, and
        // fails of those that have the rest.
        List<FixtureTemplate> named = new ArrayList<>();
        for (ValuesAStatementNames.Named each : names) {
            if (each instanceof ValuesAStatementNames.Named.AtValue(Value written)
                    && Witnesses.writtenAs(written, held, reading) instanceof FixtureTemplate value) {
                named.add(value);
            }
        }
        // As few as the rules allow, and each number of them the statement names within what the
        // rules allow.
        List<DeclaredBounds.CountRange> ranges = new ArrayList<>(List.of(rules));
        for (ValuesAStatementNames.Named each : sizes) {
            if (each instanceof ValuesAStatementNames.Named.Holding(BigInteger many)) {
                int count = many.min(BigInteger.valueOf(Integer.MAX_VALUE)).intValue();
                ranges.add(new DeclaredBounds.CountRange(Math.max(count, rules.least()),
                        Math.min(count, rules.most())));
            }
        }
        List<FixtureTemplate> out = new ArrayList<>();
        for (List<FixtureTemplate> chosen : subsetsFromTheEnds(named, MOST_VALUES + 1)) {
            Set<String> chosenTexts = new HashSet<>();
            chosen.forEach(each -> chosenTexts.add(each.text()));
            List<FixtureTemplate> keptOut = named.stream()
                    .filter(each -> !chosenTexts.contains(each.text())).toList();
            for (DeclaredBounds.CountRange holds : ranges) {
                if (holds.empty()) {
                    continue;
                }
                Proposals made = switch (view.shape()) {
                    case Shape.Sequence carrier -> Witnesses.holding(carrier,
                            ElementsKeptApart.at(view, List.of(), reading), chosen, keptOut, holds,
                            reading);
                    case Shape.Mapping map -> Witnesses.holding(map, List.of(), List.of(), null,
                            chosen.stream().map(key -> new Witnesses.Filed(key, null)).toList(),
                            keptOut, holds, reading);
                    default -> Proposals.NONE;
                };
                for (CompositionBudget met : made.met().figures()) {
                    stopped.add(met.figure());
                }
                FixtureTemplate worn = made.values().isEmpty() ? null
                        : WornNames.under(view.wrappers(), made.values().getFirst(), source);
                if (worn != null && !out.contains(worn) && out.size() <= MOST_VALUES) {
                    out.add(worn);
                }
            }
        }
        return out;
    }

    /**
     * The subsets of {@code members}, taken from the ends in: none of them and all of them, then
     * one and all but one, then two and all but two, and so on, each size in the order the members
     * stand — no more than {@code most} of them, so that a statement naming many values builds none
     * past what the search tries. One past the figure is enough for the caller to say it was
     * passed ({@link RowSearch#upTo}).
     *
     * <p>What a statement needs of them is not known here, and the subsets it needs are those the
     * statement's structure makes extreme: a conjunction of holding each needs all of them, a
     * disjunction one, a denial of either all but one or none. Counted up from none, a statement
     * naming more values than the search tries subsets of would meet the figure before the one it
     * needs.
     */
    static List<List<FixtureTemplate>> subsetsFromTheEnds(List<FixtureTemplate> members,
                                                          int most) {
        List<List<FixtureTemplate>> out = new ArrayList<>();
        for (int low = 0, high = members.size(); low <= high && out.size() < most;
                low++, high--) {
            choosing(members, low, most, out);
            if (high != low) {
                choosing(members, high, most, out);
            }
        }
        return out;
    }

    /**
     * Each way of choosing {@code size} of {@code members}, in the order the members stand, added
     * to {@code into} until it holds {@code most}.
     *
     * <p>Made one after the next from the positions chosen and not by recursion, so that the stack
     * does not grow with how many are chosen and the work is that of the subsets made.
     */
    private static void choosing(List<FixtureTemplate> members, int size, int most,
                                 List<List<FixtureTemplate>> into) {
        int[] at = new int[size];
        for (int each = 0; each < size; each++) {
            at[each] = each;
        }
        while (into.size() < most) {
            List<FixtureTemplate> chosen = new ArrayList<>(size);
            for (int each : at) {
                chosen.add(members.get(each));
            }
            into.add(chosen);
            int moving = size - 1;
            while (moving >= 0 && at[moving] == members.size() - size + moving) {
                moving--;
            }
            if (moving < 0) {
                return;
            }
            at[moving]++;
            for (int after = moving + 1; after < size; after++) {
                at[after] = at[after - 1] + 1;
            }
        }
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
                                       Operand.At<DecisionSubject>(
                                               DecisionSubject.AnInput(TermPath other, var _)),
                                       boolean holds, var _) when holds ->
                    sameValueAt(one, other, element, into);
            // The same statement, written as the form of the two places against nought: what a
            // comparison of two places is where it stands among others of a conjunction.
            case Proposition.Compared compared when compared.holds()
                    && compared.relation() instanceof Relation.Affine(var form, var rel)
                    && rel == Rel.EQ && form.constant().isZero() && form.coefs().size() == 2 -> {
                List<Map.Entry<Quantity, ExactRatio>> both =
                        List.copyOf(form.coefs().entrySet());
                if (both.getFirst().getValue().negated().equals(both.getLast().getValue())
                        && placeOf(both.getFirst().getKey()) instanceof TermPath one
                        && placeOf(both.getLast().getKey()) instanceof TermPath other) {
                    sameValueAt(one, other, element, into);
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

    /** Adds to {@code into} the fields down to the one of {@code one} and {@code other} that is
     *  inside {@code element}, with the other, which is outside it, where they hold the same
     *  value. */
    private static void sameValueAt(TermPath one, TermPath other, TermPath element,
                                    Map<List<String>, TermPath> into) {
        List<String> inOne = fieldsBelow(element, one);
        List<String> inOther = fieldsBelow(element, other);
        // Outside only where shown apart from the element as the value is reached: a
        // place narrowed to another reach of the element may be inside it on some row.
        if (inOne != null && inOther == null && !other.standsAtUnderOrAround(element)) {
            into.putIfAbsent(inOne, other);
        } else if (inOther != null && inOne == null && !one.standsAtUnderOrAround(element)) {
            into.putIfAbsent(inOther, one);
        }
    }

    /** The place a quantity is the value of, or null where it is anything else. */
    private static TermPath placeOf(Quantity quantity) {
        return quantity instanceof DecisionAtom.OfTheInput(NumericTerm.ValueOf(TermPath place),
                var _) ? place : null;
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

    /** What the boundary builds of {@code base} at {@code slot}, an element of the container or,
     *  of a map, the key or the value of an entry made with {@code partner}, in the container at
     *  parameter {@code at} — or null where it refuses it. Of a map it is the part that is written
     *  back as {@code base}: a map is held by its keys, and where its entries stand is no more
     *  than the order they are written in. */
    private static ObservedValue builtAlone(FixtureTemplate base, Slot slot,
                                            FixtureTemplate partner, Container container,
                                            RuleReadingContext reading,
                                            RowSearch.Building building) {
        FixtureTemplate element = container.key() == null ? base
                : slot.ofKey() ? container.entries().of(base, partner)
                : container.entries().of(partner, base);
        int size = container.filled(List.of(element)).size();
        return building.build(container.at(), container.holding(List.of(element)))
                .map(held -> switch (container.inside(held)) {
                    case ObservedValue.Sequence(List<ObservedValue> each)
                            when each.size() == size -> each.getFirst();
                    case ObservedValue.Mapping(List<ObservedValue.Entry> each)
                            when each.size() == size -> partOf(each, base, slot, reading);
                    default -> null;
                })
                .orElse(null);
    }

    /** The key or the value, as {@code slot} says, of the entry of {@code entries} that is written
     *  back as {@code base} there — or null where none is. */
    private static ObservedValue partOf(List<ObservedValue.Entry> entries, FixtureTemplate base,
                                        Slot slot, RuleReadingContext reading) {
        for (ObservedValue.Entry each : entries) {
            ObservedValue part = slot.ofKey() ? each.key() : each.value();
            if (ObservedFixtures.of(part, slot.type(), reading)
                    instanceof ObservedFixtures.Writing.Written<FixtureTemplate>(
                            FixtureTemplate written)
                    && written.equals(base)) {
                return part;
            }
        }
        return null;
    }

    /**
     * How many the collection at {@code place} may hold, whatever rows are written: what its own
     * type's rules and those of the record holding it leave, which is the count's own reading
     * ({@link CountDomain}) and the one the boundary refuses a collection by.
     */
    private static DeclaredBounds.CountRange mayHold(TermPath place, InputReading read) {
        NumericDomain.Bounds may = UndividedByARelation.howManyMayBeHeld(place, read,
                read.quantities().region());
        return may == null ? new DeclaredBounds.CountRange(0, Integer.MAX_VALUE)
                : new DeclaredBounds.CountRange(CountDomain.leastFrom(may.min()),
                        CountDomain.mostFrom(may.max()));
    }

    /**
     * The fewest elements the container is held with: one, or where the rules of its type ask
     * for more, that many. It is asked of the count's reading and not found by building
     * containers until the boundary takes one.
     */
    private static int fewestHeld(TermPath container, InputReading read) {
        return Math.max(1, mayHold(container, read).least());
    }

    /**
     * What each entry of a map made here is made of, a key and a value. An entry is written as the
     * pair and the pair is not read back from what is written, so the parts are kept beside it.
     * Only added to, and an entry's parts are what it was made of whenever it is asked, which is
     * what leaves everything that reads it a function of its arguments.
     */
    private static final class Entries {

        private final Map<FixtureTemplate, List<FixtureTemplate>> parts = new HashMap<>();

        /** The entry of {@code key} and {@code value}. */
        FixtureTemplate of(FixtureTemplate key, FixtureTemplate value) {
            FixtureTemplate entry = FixtureTemplate.entry(key, value);
            parts.putIfAbsent(entry, List.of(key, value));
            return entry;
        }

        FixtureTemplate keyOf(FixtureTemplate entry) {
            return parts.get(entry).getFirst();
        }

        FixtureTemplate valueOf(FixtureTemplate entry) {
            return parts.get(entry).getLast();
        }
    }

    /**
     * Where values are tried for a statement to be asked of: the elements of the container, or the
     * keys of a map's entries.
     *
     * @param root  where the statement reads it
     * @param type  its type
     * @param ofKey whether it is a key, which an entry needs two of that differ
     */
    private record Slot(TermPath root, Type type, boolean ofKey) {}

    /**
     * The container the elements are counted in, as a parameter of the behavior.
     *
     * @param at    which parameter it is
     * @param place where it stands
     * @param wrap  the container holding the elements it is handed, as a value of the type of the
     *              parameter, under the names that type wears
     * @param size  the fewest elements the boundary builds it with ({@link #fewestHeld})
     * @param overAgain whether it may hold an element over again
     * @param key       the type of the keys of a map, null where it is not one
     * @param writtenKeys the keys the model writes in it
     * @param entries   of a map, what each entry made for it is made of
     * @param keyPool   of a map, keys that differ, enough to put the fewest entries it is held with
     *                  under: fixed with the container, so that what {@link #filled} fills a map
     *                  with is a function of the elements it is given
     * @param mayHold   how many the collection at a place of the container's elements may hold
     */
    private record Container(int at, TermPath place,
                             Function<List<FixtureTemplate>, FixtureTemplate> wrap,
                             List<TypeSymbol> worn, int size, boolean overAgain, Type key,
                             List<FixtureTemplate> writtenKeys, Entries entries,
                             List<FixtureTemplate> keyPool,
                             Function<TermPath, DeclaredBounds.CountRange> mayHold) {

        /** What the boundary built of the container, with the names it wears taken off. */
        ObservedValue inside(ObservedValue built) {
            return ObservedValue.inside(worn, built);
        }

        /**
         * {@code elements}, with the last of them held over again up to the fewest the container is
         * held with: the statement holds of the repeats as it does of that element. A map holds an
         * entry under a key once, so the last entry's value is put under keys the elements are not
         * under, and the map holds fewer than the fewest where the keys tried run out.
         */
        List<FixtureTemplate> filled(List<FixtureTemplate> elements) {
            List<FixtureTemplate> out = new ArrayList<>(elements);
            if (key == null) {
                while (out.size() < size) {
                    out.add(elements.getLast());
                }
                return out;
            }
            List<FixtureTemplate> under = new ArrayList<>();
            elements.forEach(each -> under.add(entries.keyOf(each)));
            FixtureTemplate value = entries.valueOf(elements.getLast());
            for (FixtureTemplate each : keyPool) {
                if (out.size() >= size) {
                    break;
                }
                if (!under.contains(each)) {
                    under.add(each);
                    out.add(entries.of(each, value));
                }
            }
            return out;
        }

        /** The container holding {@link #filled} {@code elements}. */
        FixtureTemplate holding(List<FixtureTemplate> elements) {
            return wrap.apply(filled(elements));
        }
    }
}
