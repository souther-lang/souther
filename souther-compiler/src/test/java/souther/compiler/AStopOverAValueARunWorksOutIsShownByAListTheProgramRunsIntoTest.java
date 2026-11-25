package souther.compiler;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import org.junit.jupiter.params.provider.ValueSource;

import souther.compiler.inputs.AStopShown;
import souther.compiler.inputs.InputFact;
import souther.compiler.inputs.StepWhereARunMayStop;
import souther.compiler.inputs.StepWhereAStopIsNotShown;
import souther.compiler.inputs.WhatIsShownOfAStop;
import souther.compiler.inputs.WhyAStopIsNotShown;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertAll;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A stop shown at an operation over a value a run works out, which no number of the input is, rests
 * on an input, and the program run on that input stops there, as {@link StopsHeldToTheRuns} holds
 * what is said of where a run stops to the runs.
 *
 * <p>Which input the stop is shown by is no claim: a search that puts the value at another input
 * that stops as well is as right. Each stop shown is built into an input as it says — the lists of
 * the length it names holding the element it names, and the numbers at the places it names — and
 * run, and the run stops first at the step the stop is shown at. A witness of a list longer than one
 * is built of is held by no run, and is written down ({@link #TOO_LONG_TO_RUN}).
 *
 * <p>The other direction is held by the controls: a form no run stops in, and one whose stop is not
 * one a row of the way is shown to get, have no stop shown, nor has a list of elements no value
 * of their type exists for, nor one longer than a list is.
 *
 * <p>The forms over numbers are the behaviors of one model, compiled once; the two over records
 * have a model of their own each.
 */
class AStopOverAValueARunWorksOutIsShownByAListTheProgramRunsIntoTest {

    private static final Adequacy.Asked ASKED = new Adequacy.Asked(Adequacy.Level.OFF, false);

    /** The input every form over numbers takes: a list of none and one of the greatest number,
     *  and nought and the greatest number. */
    private static final StopsHeldToTheRuns.Input INPUT = new StopsHeldToTheRuns.Input("demo", "In",
            Map.of("ds", List.of(List.of(), List.of(Long.MAX_VALUE)),
                    "q", List.of(0L, Long.MAX_VALUE)));

    /**
     * A comparison on {@code ds} and {@code q} a stop is shown of.
     *
     * @param operation the operation, as written, a stop is to be shown in; null where any is
     */
    private record Form(String comparison, String operation) {

        Form(String comparison) {
            this(comparison, null);
        }
    }

    /** The forms some claims of which no run is built to hold, each with how many for why. Any
     *  other reason, or another claim for one of these, is refused. A size of a list past the
     *  type is a list too long to build and run: its witness is one, and the rows every run stops
     *  at weigh its length, which no run here is about. */
    private static final Map<String, Map<StopsHeldToTheRuns.NotHeld, Integer>> TOO_LONG_TO_RUN =
            Map.of("aSizeOfTheLongestAListCanBePassingTheType", Map.of(
                    StopsHeldToTheRuns.NotHeld.A_WITNESS_LONGER_THAN_IS_RUN, 1,
                    StopsHeldToTheRuns.NotHeld.ROWS_OVER_WHAT_IS_NOT_WEIGHED_HERE, 1));

    /** The forms a run of the grid stops at a step of that is said not resolved, with why. */
    private static final Map<String, Set<Enum<?>>> NOT_SHOWN_WHERE_A_RUN_STOPS =
            new LinkedHashMap<>();

    /** Forms over a list of numbers, each a behavior of the one model of them. */
    private static final Map<String, Form> STOPPING = new LinkedHashMap<>();

    /** Comparisons over a list of numbers no row is shown to stop in. */
    private static final Map<String, Form> NOT_SHOWN = new LinkedHashMap<>();

    private static final String MORE_WAYS_THAN_THE_FIGURE =
            "aListWrittenOutOfMoreElementsThanTheFigure";

    private static final String MORE_CHOICES_THAN_THE_FIGURE =
            "aStepThatChoosesMoreTimesThanTheFigure";

    /** A walk of a step that answers what it carried where the element is not above it, by each
     *  of {@code choices} comparisons in turn, and the element where it is above it. */
    private static String stepOfChoices(int choices) {
        String[] notAbove = {"<", "<=", "=="};
        StringBuilder step = new StringBuilder();
        for (int at = 0; at < choices; at++) {
            step.append("if l ").append(notAbove[at % notAbove.length]).append(" w then w else ");
        }
        return "List.fold((w, l) -> " + step + "l, 0, ds)";
    }

    private static final String WALK = "List.fold((w, l) -> if l > w then l else w, 0, ds)";

    /** A type some value of exists: a pair the first of which is below the second. */
    private static final String SOME_VALUE = "data P = { a: Int, b: Int } invariant a < b\n";

    /** A type no value of exists: no whole number is the sum and the product of two others. */
    private static final String NO_VALUE =
            "data P = { a: Int, b: Int } invariant a * b == 2 && a + b == 2\n";

    /** Two elements of a type passes the type of a size. */
    private static final Form TWO_OF_A_TYPE = new Form(
            "List.length(ds) * 4611686018427387904 >= 1");

    static {
        // the element a call answers is the only one of a list of one, which is the greatest
        STOPPING.put("theElementOfAListOfOne", new Form(
                "Option.withDefault(0, List.max(ds)) + 1 <= 10"));
        // a step on each element, the rows every run stops at being of the element itself
        STOPPING.put("aStepOnEachElement", new Form("List.any(x -> x + 1 > 5, ds)"));
        // the greatest of a list written out is the element no other is past
        STOPPING.put("theGreatestOfAListWrittenOut", new Form(
                "Option.withDefault(0, List.max([q, 3])) + 1 >= 3"));
        // a value of the most ways a stop is looked for by is looked for by them all
        STOPPING.put("theMostWaysAStopIsLookedForBy", new Form(
                "Option.withDefault(0, List.max([q, 1, 2, 3, 4, 5, 6, 7])) + 1 >= 3"));
        // what makes up the list is worked out before the operation over its greatest: the stop in
        // the element is the one that is held to the run
        STOPPING.put("anElementOfAListWrittenOutWorkedOutFirst", new Form(
                "Option.withDefault(0, List.max([q + 1, 3])) + 1 >= 3", "i.q + 1"));
        // the operation over the greatest, which a run getting past the element stops in at a
        // value no search tried
        NOT_SHOWN_WHERE_A_RUN_STOPS.put("anElementOfAListWrittenOutWorkedOutFirst",
                Set.of(WhyAStopIsNotShown.NO_VALUE_FOUND_WITHIN_WHAT_IS_TRIED));
        // a walk over none comes to its seed
        STOPPING.put("theSeedOfAWalkOverNone", new Form(
                "List.fold((w, l) -> if l > w then l else w, 9223372036854775807, ds) + 1 >= 3"));
        // a walk over one comes to what its step answers of the seed and that element
        STOPPING.put("theElementOfAWalkWhoseStepChoosesAFewTimes", new Form(
                stepOfChoices(2) + " + 1 <= 10"));
        STOPPING.put("theElementOfAWalkOverOne", new Form(WALK + " + 1 <= 10"));
        // what a run works out first is got past: the sum of what the default comes to and
        // {@code q + 1} is worked out after {@code q + 1}, so a run is shown to stop in it at an
        // input where {@code q + 1} does not
        STOPPING.put("theOperationAfterOneWorkedOutFirst", new Form(
                "Option.withDefault(0, List.max(ds)) + 1 + (q + 1) <= 10", "i.ds[*] + i.q + 2"));
        // a list as long as the longest a size's passing the type is asked of, which is one a list
        // can be
        STOPPING.put("aSizeOfTheLongestAListCanBePassingTheType", new Form(
                "List.length(ds) * 4294967300 >= 1"));
        // a step every element is handed, past its type whatever the element is, is got to only
        // where the list holds one: a list of none stops nowhere
        STOPPING.put("aStepOfEveryElementPastItsTypeWhateverTheElement", new Form(
                "List.length(List.map(x -> ((x - x) + 9223372036854775807) + 1, ds)) >= 1"));

        // a walk that keeps only what is below nought comes to a number the operation keeps
        // within the type, whichever arm of its step is taken
        NOT_SHOWN.put("aWalkKeepingWhatIsBelowNought", new Form(
                "List.fold((w, l) -> if l < 0 then l else w, 0, ds) + 1 <= 10"));
        // the arm that opens the element is worked out where the list holds none, which it never
        // is there
        NOT_SHOWN.put("anArmNoRunTakes", new Form(
                "(if List.length(ds) == 0 then Option.withDefault(0, List.max(ds)) + 1 else 0)"
                        + " >= 2"));
        // a size past what a list holds is no size of a list: the longest passes nothing here
        NOT_SHOWN.put("aSizeOfTheLongestAListCanBeNotPassingTheType", new Form(
                "List.length(ds) * 4294967296 >= 1"));
        // a value of more ways than a site is looked at by is no more than the figure of ways
        NOT_SHOWN.put(MORE_CHOICES_THAN_THE_FIGURE, new Form(stepOfChoices(10) + " + 1 <= 10"));
        NOT_SHOWN.put(MORE_WAYS_THAN_THE_FIGURE, new Form(
                "Option.withDefault(0, List.max([q, 1, 2, 3, 4, 5, 6, 7, 8])) + 1 >= 3"));
    }

    /** The model of every form over a list of numbers, compiled once: the behavior {@code b} of
     *  each is its comparison, and the behavior {@code p} leaves out what the stop is in. */
    private static final class OverNumbers {

        static final List<Form> FORMS = Stream.concat(STOPPING.values().stream(),
                NOT_SHOWN.values().stream()).toList();

        static final Compilation COMPILED = ACompiledModel.measured(
                modelOf("", "Int", FORMS), ASKED);

        static final ClassLoader LOADER = COMPILED.loaderSayingWhereRunsStop("demo").orElseThrow(
                () -> new AssertionError("the module is generated to say where runs stop"));

        static String behavior(String prefix, Form form) {
            return prefix + FORMS.indexOf(form);
        }
    }

    static Stream<String> stopping() {
        return STOPPING.keySet().stream();
    }

    static Stream<String> notShown() {
        return NOT_SHOWN.keySet().stream();
    }

    @ParameterizedTest
    @MethodSource("stopping")
    void aStopShownRestsOnAnInputTheProgramRunsIntoItAt(String name) {
        Form form = STOPPING.get(name);
        String behavior = OverNumbers.behavior("b", form);
        List<WhatIsShownOfAStop> said =
                StopsHeldToTheRuns.saidOf(OverNumbers.COMPILED, "demo", behavior);
        List<AStopShown> shown = shown(OverNumbers.COMPILED, behavior);
        StopsHeldToTheRuns.Held held = StopsHeldToTheRuns.heldTo(said, new StopsHeldToTheRuns.Runs(
                OverNumbers.COMPILED, OverNumbers.LOADER, INPUT, behavior, said));
        assertAll(
                () -> assertFalse(shown.isEmpty(), "a stop is shown"),
                () -> assertTrue(form.operation() == null || shown.stream()
                                .anyMatch(each -> each.operation().equals(form.operation())),
                        "the stop in " + form.operation() + " is shown: " + shown),
                () -> assertEquals(List.of(), held.unheld(),
                        "what is said of a step is what the runs do there"),
                () -> assertEquals(TOO_LONG_TO_RUN.getOrDefault(name, Map.of()),
                        held.notHeldBecause(), "every claim is held to a run, but for the"
                                + " reasons written down: " + held.notHeldTo()),
                () -> assertEquals(NOT_SHOWN_WHERE_A_RUN_STOPS.getOrDefault(name, Set.of()),
                        held.notShownBecause(), "a run stops at a step said not resolved, for"
                                + " the reasons written down: " + held.notShown()),
                () -> assertEquals(List.of(), held.notAbout(),
                        "every claim of every run is about some run of the grid"));
    }

    /**
     * A witness that names a list's length and not its element is held to every element the
     * grid takes there, the grid as widened by the claims and not only what the input gives: the
     * input gives the greatest number alone, and a list of one below it, which the rows every run
     * stops at put in the grid, runs past the step. Said of the element, the stop is held.
     */
    @Test
    void aWitnessNamingNoElementIsHeldToEveryElementTheGridTakes() {
        String behavior = OverNumbers.behavior("b", STOPPING.get("aStepOnEachElement"));
        List<WhatIsShownOfAStop> said =
                StopsHeldToTheRuns.saidOf(OverNumbers.COMPILED, "demo", behavior);
        List<WhatIsShownOfAStop> lengthOnly = new ArrayList<>();
        boolean dropped = false;
        for (WhatIsShownOfAStop each : said) {
            if (each instanceof StepWhereARunMayStop stops && !stops.shown().isEmpty()) {
                List<AStopShown> shown = new ArrayList<>();
                for (AStopShown one : stops.shown()) {
                    List<InputFact> structure = one.structure().stream()
                            .filter(fact -> !(fact instanceof InputFact.ListElement)).toList();
                    dropped |= structure.size() < one.structure().size();
                    shown.add(new AStopShown(one.operation(), one.at(), structure));
                }
                lengthOnly.add(new StepWhereARunMayStop(stops.at(), shown, stops.constructions(),
                        stops.everyRunStops(), stops.keeping()));
            } else {
                lengthOnly.add(each);
            }
        }
        assertTrue(dropped, "the witness names the element: " + said);
        StopsHeldToTheRuns.Runs runs = new StopsHeldToTheRuns.Runs(OverNumbers.COMPILED,
                OverNumbers.LOADER, INPUT, behavior, said);

        assertEquals(Set.of(), StopsHeldToTheRuns.heldTo(said, runs).refused());
        assertEquals(Set.of(StopsHeldToTheRuns.Claim.A_STOP_SHOWN),
                StopsHeldToTheRuns.heldTo(lengthOnly, runs).refused());
    }

    /**
     * A list whose elements a witness names nothing of comes to as many lists as each element's
     * values multiplied, and past the most that are run it is held to none — counted so that no
     * count of them is past what a long holds: sixty-three elements of two values each are two
     * to the sixty-third lists, which a count that went round to below nought would take as few.
     */
    @Test
    void aWitnessOfMoreListsThanAreRunIsHeldToNoneHoweverManyItComesTo() {
        String behavior = OverNumbers.behavior("b", STOPPING.get("aStepOnEachElement"));
        List<WhatIsShownOfAStop> said =
                StopsHeldToTheRuns.saidOf(OverNumbers.COMPILED, "demo", behavior);
        InputFact.ListLength length = said.stream()
                .filter(StepWhereARunMayStop.class::isInstance)
                .map(StepWhereARunMayStop.class::cast)
                .flatMap(each -> each.shown().stream())
                .flatMap(each -> each.structure().stream())
                .filter(InputFact.ListLength.class::isInstance)
                .map(InputFact.ListLength.class::cast).findFirst()
                .orElseThrow(() -> new AssertionError("a witness names a list: " + said));
        StopsHeldToTheRuns.Runs runs = new StopsHeldToTheRuns.Runs(OverNumbers.COMPILED,
                OverNumbers.LOADER, INPUT, behavior, said);

        assertEquals(StopsHeldToTheRuns.NotHeld.A_WITNESS_COMPLETED_TO_MORE_THAN_ARE_RUN,
                runs.completions(List.of(), List.of(new InputFact.ListLength(length.list(), 63)))
                        .notBuilt());
    }

    @ParameterizedTest
    @MethodSource("notShown")
    void noStopIsShownWhereNoRowIsShownToGetThere(String name) {
        assertEquals(List.of(), shown(OverNumbers.COMPILED,
                OverNumbers.behavior("b", NOT_SHOWN.get(name))));
    }

    /** A value made more ways than the figure of a site's search allows is a search cut short, and
     *  is said so: it is no value that no way is known for. Whatever the ways are made of, the
     *  elements of a list written out and the arms of a step alike. */
    @ParameterizedTest
    @ValueSource(strings = {MORE_WAYS_THAN_THE_FIGURE, MORE_CHOICES_THAN_THE_FIGURE})
    void aValueOfMoreWaysThanTheFigureIsLeftUnresolvedForWantOfIt(String name) {
        assertEquals(List.of(WhyAStopIsNotShown.NO_VALUE_FOUND_WITHIN_WHAT_IS_TRIED),
                whyNotShown(OverNumbers.COMPILED, OverNumbers.behavior("b", NOT_SHOWN.get(name))));
    }

    /** Two elements of a type some value of exists are a list of two, which a stop is shown at. */
    @Test
    void aListOfElementsAValueOfTheirTypeExistsForIsShownAStop() {
        Compilation compilation = ACompiledModel.measured(
                modelOf(SOME_VALUE, "P", List.of(TWO_OF_A_TYPE)), ASKED);
        assertFalse(shown(compilation, "b0").isEmpty());
    }

    /** A list of two of a type no value of exists is no list: it holds none, and a size of none
     *  passes nothing. */
    @Test
    void aListOfElementsNoValueOfTheirTypeExistsForIsShownNoStop() {
        Compilation compilation = ACompiledModel.measured(
                modelOf(NO_VALUE, "P", List.of(TWO_OF_A_TYPE)), ASKED);
        assertEquals(List.of(), shown(compilation, "b0"));
    }

    /** The model of {@code forms} over a list of {@code element}, under {@code types}. */
    private static String modelOf(String types, String element, List<Form> forms) {
        StringBuilder model = new StringBuilder("module demo\n\n" + types
                + "\ndata In = { ds: List<" + element + ">, q: Int }\ndata Out = Int\n");
        for (int at = 0; at < forms.size(); at++) {
            model.append("\nbehavior b").append(at).append(" : (i: In) -> Out constructs Out\n")
                    .append("let b").append(at).append(" (i) = Out { value = if ")
                    .append(onTheInput(forms.get(at).comparison())).append(" then 1 else 2 }\n");
        }
        return model.toString();
    }

    private static String onTheInput(String text) {
        return text.replaceAll("\\bds\\b", "i.ds").replaceAll("\\bq\\b", "i.q");
    }

    /** Every stop shown of {@code behavior}. */
    private static List<AStopShown> shown(Compilation compilation, String behavior) {
        List<AStopShown> out = new ArrayList<>();
        for (WhatIsShownOfAStop each : StopsHeldToTheRuns.saidOf(compilation, "demo", behavior)) {
            if (each instanceof StepWhereARunMayStop stops) {
                out.addAll(stops.shown());
            }
        }
        return out;
    }

    /** Why a stop of {@code behavior} is not shown, where it is one the report says is not. */
    private static List<WhyAStopIsNotShown> whyNotShown(Compilation compilation,
                                                         String behavior) {
        List<WhyAStopIsNotShown> out = new ArrayList<>();
        for (WhatIsShownOfAStop each : StopsHeldToTheRuns.saidOf(compilation, "demo", behavior)) {
            if (each instanceof StepWhereAStopIsNotShown open) {
                open.notShown().forEach(one -> out.add(one.why()));
            }
        }
        return out;
    }
}
