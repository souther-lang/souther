package souther.compiler;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import souther.compiler.inputs.AStopShown;
import souther.compiler.inputs.RuleWhereARunMayStop;
import souther.compiler.inputs.RuleWhereAStopIsNotShown;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.WhatIsShownOfAStop;
import souther.compiler.partition.Partitions;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.runtime.ConstraintViolation;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertAll;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A stop the report shows at an operation of whole numbers is one the program runs into, and a run
 * that stops is never left unsaid.
 *
 * <p>The truth is the program run: each behavior is compiled and run, and a run that stops is a
 * {@code ConstraintViolation}, whose message says whether a number went past its range or a
 * divisor was nought, so a stop shown at an operation is held to ending for that reason and not
 * for the other, which is what an operation worked out before it that stops first would be. The
 * run of the numbers a stop rests on stops whatever the places the
 * stop does not name hold, which is tried over every value of a small grid: a place a stop does not
 * name is a place nothing before the operation or after it asks anything of, so a stop shown past
 * a quotient worked out after the operation is held to a divisor of every value, nought included.
 * The way to the comparison is written in the program, so a run off it stops at nothing, and the
 * numbers a stop rests on are held to it as well.
 *
 * <p>The second direction is held to the grid alone: some run of it stops, and the findings say
 * something of the operations, a stop shown or one not resolved. And a stop is shown of a form
 * that says it is {@code required}: every run of its way stops, which the program says and this
 * does not take on trust, and what a run works out before the stop is nothing this compiler cannot
 * say it gets past. How the report words a finding is held elsewhere, and so is which operation of
 * the same reason a stop is at.
 *
 * <p>Each form is a case of its own, one model of one behavior, and a form is in the list for the
 * mechanism that turns its case red where it is taken out. The grid is the three numbers that
 * decide them, so a case costs what compiling one model does.
 */
class AStopShownAtAnOperationIsOneTheProgramRunsIntoTest {

    private static final String GREATEST = "9223372036854775807";

    /** What a run of each kind of stop says it stops for. */
    private static final String INT_OVERFLOW = "Int overflow";
    private static final String DIVISION_BY_ZERO = "division by zero";

    /** The fewest numbers that decide every form below: nought, which a divisor is held at, one,
     *  which a branch is taken at, and the end of an {@code Int}, which a sum passes. */
    private static final List<Long> WHOLE = List.of(0L, 1L, Long.MAX_VALUE);

    /**
     * A comparison, and the way the program takes to it.
     *
     * @param required whether a stop is to be shown of it: every run of the way stops, which the
     *                 program says ({@link #everyRunOfTheWayStops}), and nothing a run works out
     *                 before the stop is a thing this compiler cannot say it gets past
     */
    private record Form(String way, String comparison, boolean required) {

        Form(String way, String comparison) {
            this(way, comparison, false);
        }
    }

    private static final Map<String, Form> FORMS = new LinkedHashMap<>();

    static {
        // a quotient worked out after the sum is not got to, so is not asked to be away from
        // nought: the way holds the divisor there
        FORMS.put("aQuotientAfterTheSum", new Form("q >= " + GREATEST + " && p == 0",
                "Rational.toInt(DOWN, (q + 1) / p) >= 2", true));
        // a quotient beside the sum and worked out after it is not asked either: the run ends in
        // the sum, not at the divisor it holds at nought
        FORMS.put("aQuotientBesideAndAfterTheSum", new Form("q >= " + GREATEST + " && p == 0",
                "(q + 1) + Rational.toInt(DOWN, e / p) >= 2", true));
        // nor is a branch that stands after it, whose call ends a run for what nothing says
        FORMS.put("aBranchAfterTheSum", new Form("q >= " + GREATEST,
                "Rational.toInt(DOWN, (q + 1) / p) + (if e > 0 then h(e) else 0) >= 2", true));
        // a quotient is stopped at all the same, with what stands after it left untold
        FORMS.put("aCallAfterTheQuotient", new Form("p == 0",
                "Rational.toInt(DOWN, e / p) + h(e) >= 2", true));
        // a quotient worked out before the sum is got past: the stop is where its divisor is not
        // nought, and where its divisor is no form of the input's numbers, it is not shown
        FORMS.put("aQuotientBeforeTheSum", new Form("q >= " + GREATEST,
                "Rational.toInt(DOWN, (e / p) / (q + 1)) >= 2"));
        FORMS.put("aQuotientOfNoFormBeforeTheSum", new Form("q >= " + GREATEST,
                "Rational.toInt(DOWN, (e / (p * p)) / (q + 1)) >= 2"));
        // the body of a let has no place among what a run always works out, and is worked out
        // after the sum all the same: a run that stops at the sum has not got to it
        FORMS.put("aLetBodyAfterTheSum", new Form("q >= " + GREATEST,
                "(q + 1) + { let t = e\n q + 2 } >= 2", true));
        // a call before the sum that stops every run of the way is not got past
        FORMS.put("aCallBeforeTheSumThatStops", new Form("q >= " + GREATEST + " && p == 0",
                "h(p) + (q + 1) >= 2"));
    }

    static Stream<String> forms() {
        return FORMS.keySet().stream();
    }

    /** One form is one model of one behavior, which is as much as the claim about it asks. */
    @ParameterizedTest
    @MethodSource("forms")
    void aStopShownAtAnOperationIsOneTheProgramRunsInto(String name) throws Exception {
        Form form = FORMS.get(name);
        String model = """
                module demo

                data In = { e: Int, p: Int, q: Int }
                data Out = Int
                %s
                behavior b : (i: In) -> Out constructs Out
                let b (i) = Out { value = if %s then (if %s then 1 else 2) else 3 }
                """.formatted(form.comparison().contains("h(")
                        ? "\nbehavior h : (z: Int) -> Int\nlet h (z) = Rational.toInt(DOWN, 1 / z)\n"
                        : "", onTheInput(form.way()), onTheInput(form.comparison()));
        Compilation compilation = ACompiledModel.measured(model,
                new Adequacy.Asked(Adequacy.Level.OFF, false));
        BytesClassLoader loader = new BytesClassLoader(compilation.classes(),
                AStopShownAtAnOperationIsOneTheProgramRunsIntoTest.class.getClassLoader());
        Object behavior = Emitted.behavior(loader, "demo", "b").getConstructor().newInstance();
        Partitions.Partitioning divided =
                compilation.db().ask(new Adequacy.Divided("demo", "b")).value();
        boolean saidSomething = false;
        boolean aStopShown = false;
        List<String> shownAndItsRunDoesNotStop = new ArrayList<>();
        for (WhatIsShownOfAStop each : divided.stopsShown()) {
            if (each instanceof RuleWhereARunMayStop stops) {
                saidSomething |= !stops.shown().isEmpty() || !stops.everyRunStops().isEmpty();
                aStopShown |= !stops.shown().isEmpty();
                for (AStopShown shown : stops.shown()) {
                    String ends = shown.operation().startsWith("division")
                            ? DIVISION_BY_ZERO : INT_OVERFLOW;
                    for (Map<String, Object> in : inputsOf(shown)) {
                        String stoppedFor = stoppedFor(loader, behavior, in);
                        if (stoppedFor == null || !stoppedFor.startsWith(ends)) {
                            shownAndItsRunDoesNotStop.add(shown.operation() + " at " + in
                                    + " ends for " + stoppedFor);
                        }
                    }
                }
            } else if (each instanceof RuleWhereAStopIsNotShown open) {
                saidSomething |= !open.notShown().isEmpty();
            }
        }
        boolean said = saidSomething;
        boolean shown = aStopShown;
        boolean someRunStops = someRunStops(loader, behavior);
        boolean everyRunOfTheWayStops = form.required() && everyRunOfTheWayStops(loader, behavior);
        assertAll(
                () -> assertEquals(List.of(), shownAndItsRunDoesNotStop,
                        "told that a run stops at an operation, and the run of the numbers the "
                                + "stop rests on does not stop"),
                () -> assertTrue(said || !someRunStops,
                        "a run of the grid stops and the findings say nothing of an operation"),
                () -> assertTrue(!form.required() || everyRunOfTheWayStops,
                        "a form said to stop every run of its way, and a run of the grid on the"
                                + " way gets past what it works out"),
                () -> assertTrue(!everyRunOfTheWayStops || shown,
                        "every run of the way stops, nothing it works out first is one this"
                                + " compiler cannot say it gets past, and no stop is shown"));
    }

    /** {@code text} over the fields of the input {@code i}. */
    private static String onTheInput(String text) {
        return text.replaceAll("\\be\\b", "i.e").replaceAll("\\bp\\b", "i.p")
                .replaceAll("\\bq\\b", "i.q");
    }

    /** The numbers {@code shown} rests on, with each place it does not name at every value of the
     *  grid. */
    private static List<Map<String, Object>> inputsOf(AStopShown shown) {
        Map<String, Long> named = new LinkedHashMap<>();
        for (AStopShown.NumberAt number : shown.at()) {
            named.put(((TermPath.Step.Field) number.place().steps().getLast()).name(),
                    number.number().longValueExact());
        }
        List<Map<String, Object>> out = new ArrayList<>();
        for (long e : named.containsKey("e") ? List.of(named.get("e")) : WHOLE) {
            for (long p : named.containsKey("p") ? List.of(named.get("p")) : WHOLE) {
                for (long q : named.containsKey("q") ? List.of(named.get("q")) : WHOLE) {
                    out.add(Map.of("e", e, "p", p, "q", q));
                }
            }
        }
        return out;
    }

    /**
     * Whether some run of the grid stops and none gets past the way's comparison. A run off the
     * way answers {@code 3} and a run on it that stops answers nothing, so a run that answers one
     * or two is a run on the way that does not stop.
     */
    private static boolean everyRunOfTheWayStops(ClassLoader loader, Object behavior)
            throws Exception {
        boolean someStops = false;
        for (long e : WHOLE) {
            for (long p : WHOLE) {
                for (long q : WHOLE) {
                    Map<String, Object> raw = Map.of("e", e, "p", p, "q", q);
                    if (stoppedFor(loader, behavior, raw) != null) {
                        someStops = true;
                    } else {
                        Object out = Codecs.apply(behavior, Codecs.decoded(loader, "demo.In", raw));
                        if (!String.valueOf(Codecs.encode(loader, "demo.Out", out)).equals("3")) {
                            return false;
                        }
                    }
                }
            }
        }
        return someStops;
    }

    private static boolean someRunStops(ClassLoader loader, Object behavior) throws Exception {
        for (long e : WHOLE) {
            for (long p : WHOLE) {
                for (long q : WHOLE) {
                    if (stoppedFor(loader, behavior, Map.of("e", e, "p", p, "q", q)) != null) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    /** What the run of {@code raw} stops for, the message of its {@code ConstraintViolation}:
     *  null where it stops at nothing. */
    private static String stoppedFor(ClassLoader loader, Object behavior, Map<String, Object> raw)
            throws Exception {
        Object in = Codecs.decoded(loader, "demo.In", raw);
        try {
            Codecs.apply(behavior, in);
            return null;
        } catch (ConstraintViolation stopped) {
            return stopped.getMessage();
        }
    }
}
