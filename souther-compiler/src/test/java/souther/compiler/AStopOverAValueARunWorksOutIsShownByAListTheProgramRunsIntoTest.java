package souther.compiler;

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
 * stops there.
 *
 * <p>The truth is the program run. Each stop shown is built into an input as it says — the lists
 * of the length it names holding the element it names, and the numbers at the places it names — and
 * run, and it stops with an {@code Int} past its range. A run says that and not where, so the place
 * is held by a second run of the same input: the comparison with the operation left out, which
 * stops at nothing, so that the first run reached the operation and stopped in it.
 *
 * <p>The other direction is held by the controls: a form no run stops in, and one whose stop is not
 * one a row of the way is shown to get, have no stop shown, nor has a list of elements no value
 * of their type exists for, nor one longer than a list is.
 */
class AStopOverAValueARunWorksOutIsShownByAListTheProgramRunsIntoTest {

    private static final BigInteger GREATEST = BigInteger.valueOf(Long.MAX_VALUE);
    private static final TermPath DS = TermPath.of("i").then("ds");
    private static final TermPath Q = TermPath.of("i").then("q");

    /** The most elements a list holds, which a length the stop rests on is held to. */
    private static final int MOST_ELEMENTS = Integer.MAX_VALUE;

    /**
     * A comparison on {@code ds} and {@code q}, and what the stops shown of it rest on.
     *
     * @param before    the comparison with the operation the stop is in left out, which stops at
     *                  nothing the stop rests on; null where the form has several stops
     * @param structure the lists the one stop shown asks for, or null where which of several that
     *                  stop is is not held
     */
    private record Form(String types, String element, String comparison, String before,
                        List<AStopShown.NumberAt> at, List<InputFact> structure) {

        Form(String comparison, String before, List<AStopShown.NumberAt> at,
             List<InputFact> structure) {
            this("", "Int", comparison, before, at, structure);
        }
    }

    private static final Map<String, Form> STOPPING = new LinkedHashMap<>();

    /** Comparisons no row is shown to stop in, each with the types it is over. */
    private static final Map<String, Form> NOT_SHOWN = new LinkedHashMap<>();

    private static final String WALK = "List.fold((w, l) -> if l > w then l else w, 0, ds)";

    /** A type no value of exists: no whole number is the sum and the product of two others. */
    private static final String NO_VALUE =
            "data P = { a: Int, b: Int } invariant a * b == 2 && a + b == 2\n";

    static {
        // the element a call answers is the only one of a list of one, which is the greatest
        STOPPING.put("theElementOfAListOfOne", new Form(
                "Option.withDefault(0, List.max(ds)) + 1 <= 10",
                "Option.withDefault(0, List.max(ds)) <= 10", List.of(),
                List.of(new InputFact.ListLength(DS, 1),
                        new InputFact.ListElement(DS, 0, GREATEST))));
        // the default is what a list of none answers, and the element of a list of one is what it
        // answers otherwise: either stops, and which of them is shown is not what is held
        STOPPING.put("theDefaultOfAListOfNone", new Form(
                "Option.withDefault(9223372036854775807, List.max(ds)) + 1 >= 3", null,
                List.of(), null));
        // the greatest of a list written out is the element no other is past
        STOPPING.put("theGreatestOfAListWrittenOut", new Form(
                "Option.withDefault(0, List.max([q, 3])) + 1 >= 3",
                "Option.withDefault(0, List.max([q, 3])) >= 3",
                List.of(new AStopShown.NumberAt(Q, GREATEST)), List.of()));
        // a walk over none comes to its seed
        STOPPING.put("theSeedOfAWalkOverNone", new Form(
                "List.fold((w, l) -> if l > w then l else w, 9223372036854775807, ds) + 1 >= 3",
                "List.fold((w, l) -> if l > w then l else w, 9223372036854775807, ds) >= 3",
                List.of(), List.of(new InputFact.ListLength(DS, 0))));
        // a walk over one comes to what its step answers of the seed and that element: the
        // element where the arm that keeps it is the one taken
        STOPPING.put("theElementOfAWalkOverOne", new Form(WALK + " + 1 <= 10", WALK + " <= 10",
                List.of(), List.of(new InputFact.ListLength(DS, 1),
                        new InputFact.ListElement(DS, 0, GREATEST))));
        // what stops first is shown: the operation in the step is worked out before the one over
        // what it comes to, and a list of one holding the greatest stops there
        STOPPING.put("theOperationWorkedOutFirst", new Form(
                "Option.withDefault(0, List.max(List.map(x -> x + 1, ds))) + 1 <= 10",
                "Option.withDefault(0, List.max(List.map(x -> x, ds))) <= 10", List.of(),
                List.of(new InputFact.ListLength(DS, 1),
                        new InputFact.ListElement(DS, 0, GREATEST))));
        // a list as long as a list is, and the longest a stop is shown at: four thousand million
        // and a hundred of the length past which a number of a list's size passes the type
        STOPPING.put("theMostElementsAListHolds", new Form(
                "List.length(ds) * 4294967300 >= 1", null, List.of(),
                List.of(new InputFact.ListLength(DS, MOST_ELEMENTS))));
        // two elements of a type some value of exists
        STOPPING.put("aListOfElementsAValueOfTheirTypeExistsFor", new Form(
                "data P = { a: Int, b: Int } invariant a < b\n", "P",
                "List.length(ds) * 4611686018427387904 >= 1", null, List.of(),
                List.of(new InputFact.ListLength(DS, 2))));

        // what a list written out holds keeps the operation within the type
        NOT_SHOWN.put("aListWrittenOutKeptWithin", new Form(
                "Option.withDefault(0, List.max([1, 2])) + 1 >= 3", null, List.of(), null));
        // a test every element meets keeps what the greatest of them comes to within the type
        NOT_SHOWN.put("aTestOfEveryElementKeepsItWithin", new Form(
                "List.all(x -> x < 9223372036854775807, ds) && "
                        + "Option.withDefault(0, List.max(ds)) + 1 <= 10", null, List.of(), null));
        // a walk that keeps only what is below nought comes to a number the operation keeps
        // within the type, whichever arm of its step is taken
        NOT_SHOWN.put("aWalkKeepingWhatIsBelowNought", new Form(
                "List.fold((w, l) -> if l < 0 then l else w, 0, ds) + 1 <= 10", null, List.of(),
                null));
        // the arm that opens the element is worked out where the list holds none, which it never
        // is there
        NOT_SHOWN.put("anArmNoRunTakes", new Form(
                "(if List.length(ds) == 0 then Option.withDefault(0, List.max(ds)) + 1 else 0)"
                        + " >= 2", null, List.of(), null));
        // a list of two of a type no value exists for is no list: it holds none, and a size of
        // none passes nothing
        NOT_SHOWN.put("aListOfElementsNoValueOfTheirTypeExistsFor", new Form(NO_VALUE, "P",
                "List.length(ds) * 4611686018427387904 >= 1", null, List.of(), null));
        // a size past what a list holds is no size of a list: the longest, four thousand million
        // and nought, passes nothing, so no list is shown to pass the type
        NOT_SHOWN.put("aListLongerThanAListIs", new Form(
                "List.length(ds) * 4294967296 >= 1", null, List.of(), null));
        // a value of more ways than a site is looked at by is no more than the figure of ways
        NOT_SHOWN.put("aListWrittenOutOfMoreElementsThanTheFigure", new Form(
                "Option.withDefault(0, List.max([q, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10])) + 1 >= 3",
                null, List.of(), null));
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
        Run run = Run.of(form);
        List<AStopShown> shown = run.shown();
        assertFalse(shown.isEmpty(), "a stop is shown");
        if (form.structure() != null) {
            assertTrue(shown.stream().anyMatch(each -> each.at().equals(form.at())
                    && each.structure().equals(form.structure())),
                    "a stop shown rests on " + form.at() + form.structure() + ", of " + shown);
        }
        for (AStopShown each : shown) {
            if (!aListTheProgramIsRunOn(form, each)) {
                continue;
            }
            assertTrue(run.stoppedFor("b", each).startsWith("Int overflow"),
                    "the run of the input the stop rests on, " + each);
            if (form.before() != null) {
                assertEquals("no stop", run.stoppedFor("p", each),
                        "what is worked out before the operation, on the same input, " + each);
            }
        }
    }

    /** Whether the list a stop rests on is one this builds and runs: a list of numbers no longer
     *  than a run of it is cheap, and not one of records, which this has no input for. What is not
     *  run is held by what the stop is said to rest on alone. */
    private static boolean aListTheProgramIsRunOn(Form form, AStopShown shown) {
        return form.element().equals("Int") && shown.structure().stream().noneMatch(
                fact -> fact instanceof InputFact.ListLength(var _, int length) && length > 1_000);
    }

    @ParameterizedTest
    @MethodSource("notShown")
    void noStopIsShownWhereNoRowIsShownToGetThere(String name) {
        assertEquals(List.of(), Run.of(NOT_SHOWN.get(name)).shown());
    }

    /** One comparison, compiled as a behavior of a model beside the one that leaves out what
     *  the stop is in. */
    private record Run(Compilation compilation) {

        static Run of(Form form) {
            String model = """
                    module demo

                    %s
                    data In = { ds: List<%s>, q: Int }
                    data Out = Int

                    behavior b : (i: In) -> Out constructs Out
                    let b (i) = Out { value = if %s then 1 else 2 }
                    %s
                    """.formatted(form.types(), form.element(), onTheInput(form.comparison()),
                    form.before() == null ? "" : """
                            behavior p : (i: In) -> Out constructs Out
                            let p (i) = Out { value = if %s then 1 else 2 }
                            """.formatted(onTheInput(form.before())));
            return new Run(ACompiledModel.measured(model,
                    new Adequacy.Asked(Adequacy.Level.OFF, false)));
        }

        private static String onTheInput(String text) {
            return text.replaceAll("\\bds\\b", "i.ds").replaceAll("\\bq\\b", "i.q");
        }

        /** Every stop shown of the behavior {@code b}. */
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

        /** What the run of the input {@code shown} rests on stops for in {@code behavior}, or
         *  that it stops at nothing. */
        String stoppedFor(String behavior, AStopShown shown) throws Exception {
            BytesClassLoader loader = new BytesClassLoader(compilation.classes(),
                    AStopOverAValueARunWorksOutIsShownByAListTheProgramRunsIntoTest.class
                            .getClassLoader());
            Object run = Emitted.behavior(loader, "demo", behavior).getConstructor()
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
                Codecs.apply(run, in);
                return "no stop";
            } catch (ConstraintViolation stopped) {
                return stopped.getMessage();
            }
        }
    }
}
