package souther.compiler;

import org.junit.jupiter.api.Test;

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
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertAll;
import static org.junit.jupiter.api.Assertions.assertEquals;

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
 * something of the operations, a stop shown or one not resolved. How the report words a finding is
 * held elsewhere, and so is which operation of the same reason a stop is at.
 */
class AStopShownAtAnOperationIsOneTheProgramRunsIntoTest {

    private static final String GREATEST = "9223372036854775807";

    /** What a run of each kind of stop says it stops for. */
    private static final String INT_OVERFLOW = "Int overflow";
    private static final String DIVISION_BY_ZERO = "division by zero";

    private static final List<Long> WHOLE = List.of(0L, 1L, -1L, 3L, 4_611_686_018_427_387_904L,
            Long.MAX_VALUE, Long.MIN_VALUE);

    /** A comparison, and the way the program takes to it. */
    private record Form(String way, String comparison) {}

    private static final Map<String, Form> FORMS = new LinkedHashMap<>();

    static {
        // an operation worked out before a quotient: the quotient is not got to
        FORMS.put("aQuotientAfterTheSum", new Form("q >= " + GREATEST,
                "Rational.toInt(DOWN, (q + 1) / p) >= 2"));
        FORMS.put("aQuotientAfterTheSumByNought", new Form(
                "q >= " + GREATEST + " && p == 0", "Rational.toInt(DOWN, (q + 1) / p) >= 2"));
        // a quotient worked out before the operation: it is got past
        FORMS.put("aQuotientBeforeTheSum", new Form("q >= " + GREATEST,
                "Rational.toInt(DOWN, (e / p) / (q + 1)) >= 2"));
        FORMS.put("aQuotientByTheSum", new Form("q >= " + GREATEST,
                "Rational.toInt(DOWN, e / (q + 1)) >= 2"));
        FORMS.put("aQuotientOfNoFormBeforeTheSum", new Form("q >= " + GREATEST,
                "Rational.toInt(DOWN, (e / (p * p)) / (q + 1)) >= 2"));
        // a rounding worked out before the operation, and after it, and beside it
        FORMS.put("aRoundingBeforeTheSum", new Form("q >= " + GREATEST,
                "Rational.toInt(DOWN, (Rational.toInt(DOWN, e / p) + (q + 1)) / 2) >= 2"));
        FORMS.put("aRoundingAfterTheSum", new Form("q >= " + GREATEST,
                "(q + 1) + Rational.toInt(DOWN, e / 3) >= 2"));
        FORMS.put("aRoundingBeforeTheSumInASum", new Form("q >= " + GREATEST,
                "Rational.toInt(DOWN, e / 3) + (q + 1) >= 2"));
        FORMS.put("aRoundingOnEitherSide", new Form("q >= " + GREATEST,
                "Rational.toInt(DOWN, (q + 1) / 2) >= Rational.toInt(DOWN, e / p)"));
        // a call before the sum that stops every run of the way, and one after it
        FORMS.put("aCallBeforeTheSumThatStops", new Form("q >= " + GREATEST + " && p == 0",
                "h(p) + (q + 1) >= 2"));
        FORMS.put("aCallAfterTheSumThatStops", new Form("q >= " + GREATEST + " && p == 0",
                "(q + 1) + h(p) >= 2"));
        // the first operation of a product of three, the second of two numbers of the input
        FORMS.put("aProductOfTheInput", new Form("e >= 0", "2 * p * q >= 1000"));
        // nothing before it, nothing after it
        FORMS.put("aSumAlone", new Form("e >= 0", "p + q >= 1000"));
    }

    @Test
    void aStopShownAtAnOperationIsOneTheProgramRunsInto() throws Exception {
        List<String> names = new ArrayList<>(FORMS.keySet());
        StringBuilder model = new StringBuilder("""
                module demo

                data In = { e: Int, p: Int, q: Int }
                data Out = Int

                behavior h : (z: Int) -> Int
                let h (z) = Rational.toInt(DOWN, 1 / z)
                """);
        for (int at = 0; at < names.size(); at++) {
            Form form = FORMS.get(names.get(at));
            model.append("\nbehavior b").append(at).append(" : (i: In) -> Out constructs Out")
                    .append("\nlet b").append(at).append(" (i) = Out { value = if ")
                    .append(onTheInput(form.way())).append(" then (if ")
                    .append(onTheInput(form.comparison())).append(" then 1 else 2) else 3 }\n");
        }
        Compilation compilation = ACompiledModel.measured(model.toString(),
                new Adequacy.Asked(Adequacy.Level.OFF, false));
        BytesClassLoader loader = new BytesClassLoader(compilation.classes(),
                AStopShownAtAnOperationIsOneTheProgramRunsIntoTest.class.getClassLoader());
        TreeSet<String> shownAndItsRunDoesNotStop = new TreeSet<>();
        TreeSet<String> stopsAndNothingSaid = new TreeSet<>();
        for (int at = 0; at < names.size(); at++) {
            String name = names.get(at);
            Object behavior = Emitted.behavior(loader, "demo", "b" + at)
                    .getConstructor().newInstance();
            Partitions.Partitioning divided =
                    compilation.db().ask(new Adequacy.Divided("demo", "b" + at)).value();
            boolean saidSomething = false;
            for (WhatIsShownOfAStop each : divided.stopsShown()) {
                if (each instanceof RuleWhereARunMayStop stops) {
                    saidSomething |= !stops.shown().isEmpty() || !stops.everyRunStops().isEmpty();
                    for (AStopShown shown : stops.shown()) {
                        String ends = shown.operation().startsWith("division")
                                ? DIVISION_BY_ZERO : INT_OVERFLOW;
                        for (Map<String, Object> in : inputsOf(shown)) {
                            String stoppedFor = stoppedFor(loader, behavior, in);
                            if (stoppedFor == null || !stoppedFor.startsWith(ends)) {
                                shownAndItsRunDoesNotStop.add(name + ": " + shown.operation()
                                        + " at " + in + " ends for " + stoppedFor);
                            }
                        }
                    }
                } else if (each instanceof RuleWhereAStopIsNotShown open) {
                    saidSomething |= !open.notShown().isEmpty();
                }
            }
            if (!saidSomething && someRunStops(loader, behavior)) {
                stopsAndNothingSaid.add(name);
            }
        }
        assertAll(
                () -> assertEquals(new TreeSet<>(), shownAndItsRunDoesNotStop,
                        "told that a run stops at an operation, and the run of the numbers the "
                                + "stop rests on does not stop"),
                () -> assertEquals(new TreeSet<>(), stopsAndNothingSaid,
                        "a run of the grid stops and the findings say nothing of an operation"));
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
