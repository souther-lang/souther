package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.InputDomain;
import souther.compiler.observe.Figure;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.WorkFigure;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.IntPredicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A parameter a run of the behavior does not turn on is tried with its first value alone, so the
 * rows a search tries are spent on the parameters that can decide what it looks for. And how many
 * parameters there are is no depth of anything: rows over a great many of them are walked without
 * a call for each.
 */
class AParameterARunDoesNotTurnOnIsTriedAtItsFirstValueAloneTest {

    private static final String FLAGS = """
            module example.m

            data On
            data Off
            data Flag = On | Off

            behavior f : (a: Flag, b: Flag, c: Flag) -> Flag

            let f (a, b, c) = a
            """;

    private static List<List<RowSearch.Built>> triedWith(IntPredicate atFirst) {
        return triedWith(atFirst, 2, (_, fixture) -> Optional.of(new ObservedValue.Text(
                fixture.text())), new HashSet<>());
    }

    private static List<List<RowSearch.Built>> triedWith(IntPredicate atFirst, int howManyNamed,
                                                         RowSearch.Building building,
                                                         Set<Figure> stopped) {
        return triedWith(atFirst, howManyNamed, building, stopped, List.of());
    }

    private static List<List<RowSearch.Built>> triedWith(IntPredicate atFirst, int howManyNamed,
                                                         RowSearch.Building building,
                                                         Set<Figure> stopped,
                                                         List<List<ObservedValue>> taken) {
        Compilation compilation = Compilation.ofSource(FLAGS, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingContext context =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        InputDomain domain = InputDomain.of(sigs.get("f"), context,
                TypeCardinality.Counts.workedOutIn(context), Membership.none());
        Partitions.Partitioning partitioning =
                Partitions.of("f", domain.reading(rules), ReadAs.THE_COMPILATION_DOES);
        MeasuredInput subject = MeasuredInput.of("f", domain.reading(rules), partitioning);
        List<List<FixtureTemplate>> named = new ArrayList<>();
        subject.types().forEach(_ -> {
            List<FixtureTemplate> values = new ArrayList<>();
            for (int i = 0; i < howManyNamed; i++) {
                values.add(FixtureTemplate.string("v" + i));
            }
            named.add(values);
        });
        return RowSearch.tried(subject.types(), named, taken, subject.types()::get,
                _ -> null, atFirst, _ -> false, subject.ruleReading(), building, stopped);
    }

    @Test
    void aParameterTheRunDoesNotTurnOnHasOneValueAndTheOthersKeepTheirs() {
        List<List<RowSearch.Built>> every = triedWith(_ -> false);
        List<List<RowSearch.Built>> standing = triedWith(at -> at != 0);

        assertTrue(every.get(1).size() > 1, "a parameter has more than one value to try");
        assertEquals(every.get(0).size(), standing.get(0).size());
        assertEquals(1, standing.get(1).size());
        assertEquals(1, standing.get(2).size());
        assertEquals(every.get(1).getFirst(), standing.get(1).getFirst());
    }

    /**
     * Past the figure a parameter's values are cut at, a parameter the run does not turn on is
     * still built once and says nothing of the values it never took: the figure is for the
     * parameters whose later values the search would have tried.
     */
    @Test
    void aParameterTheRunDoesNotTurnOnBuildsOnceAndStopsNowhereHoweverManyValuesItHas() {
        int[] built = new int[3];
        Set<Figure> stopped = new HashSet<>();

        List<List<RowSearch.Built>> each = triedWith(at -> at != 0, RowSearch.MOST_VALUES + 1,
                (at, fixture) -> {
                    built[at]++;
                    return Optional.of(new ObservedValue.Text(fixture.text()));
                }, stopped);

        assertEquals(1, built[1], "built once");
        assertEquals(1, built[2], "built once");
        assertEquals(RowSearch.MOST_VALUES, built[0], "a parameter that can decide is built to the figure");
        assertEquals(1, each.get(1).size());
        assertEquals(1, stopped.size(), "the one parameter that can decide was cut at its figure");
    }

    /**
     * Looking for the first value that builds is bounded by the figure the values of a parameter
     * are tried to: where none is built by then the figure is said, and where one is built before
     * it nothing is.
     */
    @Test
    void lookingForTheFirstValueThatBuildsIsBoundedAndSaysWhereItStopped() {
        int[] built = new int[3];
        Set<Figure> stopped = new HashSet<>();

        List<List<RowSearch.Built>> none = triedWith(at -> at == 1, RowSearch.MOST_VALUES + 50,
                (at, fixture) -> {
                    built[at]++;
                    return at == 1 ? Optional.empty()
                            : Optional.of(new ObservedValue.Text(fixture.text()));
                }, stopped);

        assertEquals(null, none, "no value of the parameter is built");
        assertEquals(RowSearch.MOST_VALUES, built[1], "the figure and no more are built");
        assertTrue(stopped.contains(CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.figure()));

        List<List<RowSearch.Built>> some = triedWith(at -> at == 1, 4,
                (at, fixture) -> at == 1 && !fixture.equals(FixtureTemplate.string("v3"))
                        ? Optional.empty()
                        : Optional.of(new ObservedValue.Text(fixture.text())), new HashSet<>());

        assertEquals(FixtureTemplate.string("v3"), some.get(1).getFirst().fixture());
    }

    /**
     * A value a run's observation was cut short at is one the search did not get to try. It is
     * said where no value of the parameter was found, since the search then did not look to the
     * end, and not where one was, since that value is what the parameter is tried with.
     */
    @Test
    void whereARunWasCutShortAtAnUnreadParametersValueItIsSaidOnlyWhereNoneIsBuilt() {
        Figure cut = WorkFigure.RUNS_REPLACING_AN_ARM.at(1);
        List<List<ObservedValue>> taken = List.of(List.of(new ObservedValue.Text("v"),
                new ObservedValue.Truncated(cut), new ObservedValue.Text("v")));

        Set<Figure> none = new HashSet<>();
        triedWith(at -> at == 1, 2,
                (at, fixture) -> at == 1 ? Optional.empty()
                        : Optional.of(new ObservedValue.Text(fixture.text())), none, taken);
        Set<Figure> found = new HashSet<>();
        triedWith(at -> at == 1, 2,
                (_, fixture) -> Optional.of(new ObservedValue.Text(fixture.text())), found,
                taken);

        assertTrue(none.contains(cut), "no value was built, so what was cut short is said");
        assertTrue(!found.contains(cut), "a value was built, so it is no account");
    }

    /** The first value that does not build is passed over for the next that does. */
    @Test
    void aParameterTheRunDoesNotTurnOnIsTriedWithTheFirstValueThatBuilds() {
        List<List<RowSearch.Built>> each = triedWith(at -> at != 0, 4,
                (at, fixture) -> at == 1 && fixture.equals(FixtureTemplate.string("v0"))
                        ? Optional.empty()
                        : Optional.of(new ObservedValue.Text(fixture.text())), new HashSet<>());

        assertEquals(FixtureTemplate.string("v1"), each.get(1).getFirst().fixture());
    }

    @Test
    void theRowsTriedAreOnlyThoseOverTheParametersThatCanDecide() {
        List<List<RowSearch.Built>> every = triedWith(_ -> false);
        List<List<RowSearch.Built>> standing = triedWith(at -> at != 0);

        assertEquals(every.get(0).size() * every.get(1).size() * every.get(2).size(),
                RowSearch.rowsOf(every, new HashSet<>()).size());
        assertEquals(standing.get(0).size(),
                RowSearch.rowsOf(standing, new HashSet<>()).size());
    }

    @Test
    void rowsOverAGreatManyParametersAreNoDepthOfTheStack() {
        List<RowSearch.Built> one = List.of(new RowSearch.Built(FixtureTemplate.string("v"), null));
        List<List<RowSearch.Built>> each = new ArrayList<>();
        for (int i = 0; i < 50_000; i++) {
            each.add(one);
        }
        Set<Figure> stopped = new HashSet<>();

        List<List<RowSearch.Built>> rows = RowSearch.rowsOf(each, stopped);

        assertEquals(1, rows.size());
        assertTrue(stopped.isEmpty());
    }
}
