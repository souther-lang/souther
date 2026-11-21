package souther.compiler;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import souther.compiler.inputs.AStopShown;
import souther.compiler.inputs.InputFact;
import souther.compiler.inputs.RuleWhereARunMayStop;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.WhatIsShownOfAStop;
import souther.compiler.partition.Partitions;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.runtime.ConstraintViolation;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A stop shown at an operation over a value a run works out, which no number of the input is, rests
 * on the list or the number a row makes that value come to, and the program run on that input
 * stops.
 *
 * <p>The truth is the program run. Each stop shown is built into an input as it says — the lists
 * of the length it names holding the element it names, and the numbers at the places it names — and
 * run, and a run that does not stop with an {@code Int} past its range is a stop shown that is none.
 * The other direction is held by the controls: a form no run stops in, and one whose stop is not
 * one a row of the way is shown to get, have no stop shown.
 */
class AStopOverAValueARunWorksOutIsShownByAListTheProgramRunsIntoTest {

    private static final BigInteger GREATEST = BigInteger.valueOf(Long.MAX_VALUE);
    private static final TermPath DS = TermPath.of("i").then("ds");
    private static final TermPath Q = TermPath.of("i").then("q");

    /**
     * A comparison on {@code ds} and {@code q}, and what the stops shown of it rest on.
     *
     * @param structure the lists the one stop shown asks for, or null where which of several that
     *                  stop is is not held
     */
    private record Form(String comparison, List<AStopShown.NumberAt> at,
                        List<InputFact> structure) {}

    private static final Map<String, Form> STOPPING = new LinkedHashMap<>();

    /** Comparisons no row is shown to stop in. */
    private static final Map<String, String> NOT_SHOWN = new LinkedHashMap<>();

    static {
        // the element a call answers is the only one of a list of one, which is the greatest
        STOPPING.put("theElementOfAListOfOne", new Form(
                "Option.withDefault(0, List.max(ds)) + 1 <= 10", List.of(),
                List.of(new InputFact.ListLength(DS, 1),
                        new InputFact.ListElement(DS, 0, GREATEST))));
        // the default is what a list of none answers, and the element of a list of one is what it
        // answers otherwise: either stops, and which of them is shown is not what is held
        STOPPING.put("theDefaultOfAListOfNone", new Form(
                "Option.withDefault(9223372036854775807, List.max(ds)) + 1 >= 3", List.of(),
                null));
        // the greatest of a list written out is the element no other is past
        STOPPING.put("theGreatestOfAListWrittenOut", new Form(
                "Option.withDefault(0, List.max([q, 3])) + 1 >= 3",
                List.of(new AStopShown.NumberAt(Q, GREATEST)), List.of()));
        // a walk over none comes to its seed
        STOPPING.put("theSeedOfAWalkOverNone", new Form(
                "List.fold((w, l) -> if l > w then l else w, 9223372036854775807, ds) + 1 >= 3",
                List.of(), List.of(new InputFact.ListLength(DS, 0))));
        // a walk over one comes to what its step answers of the seed and that element: the
        // element where the arm that keeps it is the one taken
        STOPPING.put("theElementOfAWalkOverOne", new Form(
                "List.fold((w, l) -> if l > w then l else w, 0, ds) + 1 <= 10", List.of(),
                List.of(new InputFact.ListLength(DS, 1),
                        new InputFact.ListElement(DS, 0, GREATEST))));

        // what a list written out holds keeps the operation within the type
        NOT_SHOWN.put("aListWrittenOutKeptWithin",
                "Option.withDefault(0, List.max([1, 2])) + 1 >= 3");
        // a test every element meets keeps what the greatest of them comes to within the type
        NOT_SHOWN.put("aTestOfEveryElementKeepsItWithin",
                "List.all(x -> x < 9223372036854775807, ds) && "
                        + "Option.withDefault(0, List.max(ds)) + 1 <= 10");
        // a walk that keeps only what is below nought comes to a number the operation keeps
        // within the type, whichever arm of its step is taken
        NOT_SHOWN.put("aWalkKeepingWhatIsBelowNought",
                "List.fold((w, l) -> if l < 0 then l else w, 0, ds) + 1 <= 10");
        // the arm that opens the element is worked out where the list holds none, which it never
        // is there
        NOT_SHOWN.put("anArmNoRunTakes",
                "(if List.length(ds) == 0 then Option.withDefault(0, List.max(ds)) + 1 else 0) >= 2");
    }

    static Stream<String> stopping() {
        return STOPPING.keySet().stream();
    }

    static Stream<String> notShown() {
        return NOT_SHOWN.keySet().stream();
    }

    @ParameterizedTest
    @MethodSource("stopping")
    void aStopShownRestsOnTheListTheValueIsMadeAndTheProgramRunsIntoIt(String name)
            throws Exception {
        Form form = STOPPING.get(name);
        Run run = Run.of(form.comparison());
        List<AStopShown> shown = run.shown();
        assertFalse(shown.isEmpty(), "a stop is shown");
        if (form.structure() != null) {
            assertTrue(shown.stream().anyMatch(each -> each.at().equals(form.at())
                    && each.structure().equals(form.structure())),
                    "a stop shown rests on " + form.at() + form.structure() + ", of " + shown);
        }
        for (AStopShown each : shown) {
            assertEquals("Int overflow", run.stoppedFor(each).substring(0, "Int overflow".length()),
                    "the run of the input the stop rests on, " + each);
        }
    }

    @ParameterizedTest
    @MethodSource("notShown")
    void noStopIsShownWhereNoRowIsShownToGetThere(String name) {
        assertEquals(List.of(), Run.of(NOT_SHOWN.get(name)).shown());
    }

    /** What a list of none holds is none, whatever it is asked of: the way the default is
     *  taken leaves the greatest of nothing for no stop. */
    @Test
    void aListOfOneIsNotMadeWhereTheWayStatesItIsEmpty() {
        assertTrue(Run.of("(if List.length(ds) == 0 then Option.withDefault(0, List.max(ds)) + 1"
                        + " else 0) >= 2").shown().isEmpty());
    }

    /** One comparison, compiled as the one behavior of a model. */
    private record Run(Compilation compilation) {

        static Run of(String comparison) {
            String model = """
                    module demo

                    data In = { ds: List<Int>, q: Int }
                    data Out = Int

                    behavior b : (i: In) -> Out constructs Out
                    let b (i) = Out { value = if %s then 1 else 2 }
                    """.formatted(comparison.replaceAll("\\bds\\b", "i.ds")
                    .replaceAll("\\bq\\b", "i.q"));
            return new Run(ACompiledModel.measured(model,
                    new Adequacy.Asked(Adequacy.Level.OFF, false)));
        }

        /** Every stop shown of the behavior. */
        List<AStopShown> shown() {
            Partitions.Partitioning divided =
                    compilation.db().ask(new Adequacy.Divided("demo", "b")).value();
            List<AStopShown> out = new ArrayList<>();
            for (WhatIsShownOfAStop each : divided.stopsShown()) {
                if (each instanceof RuleWhereARunMayStop stops) {
                    out.addAll(stops.shown());
                }
            }
            return out;
        }

        /** What the run of the input {@code shown} rests on stops for. */
        String stoppedFor(AStopShown shown) throws Exception {
            BytesClassLoader loader = new BytesClassLoader(compilation.classes(),
                    AStopOverAValueARunWorksOutIsShownByAListTheProgramRunsIntoTest.class
                            .getClassLoader());
            Object behavior = Emitted.behavior(loader, "demo", "b").getConstructor()
                    .newInstance();
            long q = 0;
            for (AStopShown.NumberAt number : shown.at()) {
                q = number.number().longValueExact();
            }
            List<Long> ds = new ArrayList<>();
            for (InputFact fact : shown.structure()) {
                if (fact instanceof InputFact.ListLength(var _, int length)) {
                    ds = new ArrayList<>(Collections.nCopies(length, 0L));
                }
            }
            for (InputFact fact : shown.structure()) {
                if (fact instanceof InputFact.ListElement(var _, int index, BigInteger number)) {
                    ds.set(index, number.longValueExact());
                }
            }
            Object in = Codecs.decoded(loader, "demo.In", Map.of("ds", ds, "q", q));
            try {
                Codecs.apply(behavior, in);
                return "no stop";
            } catch (ConstraintViolation stopped) {
                return stopped.getMessage();
            }
        }
    }
}
