package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.PhysicalPos;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.AConstructionStopShown;
import souther.compiler.inputs.AStopShown;
import souther.compiler.inputs.RuleWhereARunMayStop;
import souther.compiler.inputs.RuleWhereAStopIsNotShown;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.WhatIsShownOfAStop;
import souther.compiler.inputs.WhyAConstructionStopIsNotShown;
import souther.compiler.partition.Partitions;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.runtime.ConstraintViolation;
import souther.runtime.InvariantFailure;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertAll;
import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A run on the way to a rule is told to stop at a construction only where some run does stop, and
 * a run that stops is never left unsaid.
 *
 * <p>The truth is the program run: each behavior is compiled and run on every input of a small
 * grid, and a run that stops is a {@code ConstraintViolation}. What the report says is held to that
 * and not to what the reading of the constructions came to, so a stop it tells where no run stops,
 * or one it says nothing of, is found by the program.
 *
 * <p>The report is asked with no rows composed or run ({@link Adequacy.Level#OFF}), so a stop it
 * tells is one shown from the model and not one a row came to.
 *
 * <p>What stops a run and is said as not resolved, rather than as a stop, is written down in
 * {@link #NOT_SHOWN}, one form each with the reason the report gives: a stop the compiler learns to
 * show moves the form out of it. A form that stops a run and says nothing of it, not even that it
 * is not resolved, is a stop dropped without a word, and none is allowed.
 *
 * <p>This holds the report and the program to one another on these inputs, and not on every
 * input: a stop only some other value reaches is not found by it.
 */
class AConstructionIsToldOfAStopWhereARunStopsThereTest {

    private static final List<Long> WHOLE = List.of(0L, -1L, 1L, 11L, Long.MAX_VALUE,
            Long.MIN_VALUE);

    private static final List<BigDecimal> DECIMAL = List.of(BigDecimal.ZERO,
            BigDecimal.ONE.negate(), BigDecimal.ONE);

    /** A behavior: what it makes, the types it constructs beside that, and its body over
     *  {@code q}, {@code d} and {@code e}. */
    private record Form(String output, String constructs, String body) {}

    private static final Map<String, Form> FORMS = new LinkedHashMap<>();

    /** What a run stops at and is said as not resolved, each with the reason said of a
     *  construction on the way. */
    private static final Map<String, WhyAConstructionStopIsNotShown> NOT_SHOWN =
            new LinkedHashMap<>();

    static {
        // one construction, over an Int and over a Decimal
        FORMS.put("plain", new Form("OneC", "Count", "OneC { a = Count(q), w = q <= 3 }"));
        FORMS.put("decimal", new Form("OneH", "Held",
                "OneH { h = Held(d), w = Decimal.compare(d, e) <= 0 }"));
        // a guard before it, after it, and one no run passes
        FORMS.put("guardBefore", new Form("OneC", "Count",
                "if q >= 0 then OneC { a = Count(q), w = q <= 3 } else OneC { a = Count(0), "
                        + "w = false }"));
        FORMS.put("guardAfter", new Form("OneC", "Count",
                "{ let m = Count(q) \n if q >= 0 then OneC { a = m, w = q <= 3 } "
                        + "else OneC { a = Count(0), w = false } }"));
        FORMS.put("onAnArmBeforeTheRule", new Form("OneC", "Count",
                "{ let m = if q >= 0 then Count(q) else Count(0) \n OneC { a = m, w = q <= 3 } }"));
        FORMS.put("onAnArmOfAnotherNumber", new Form("OneC", "Count",
                "{ let m = if Decimal.compare(d, 0.0m) < 0 then Count(q) else Count(0) \n "
                        + "OneC { a = m, w = q <= 3 } }"));
        FORMS.put("onAnArmSomeOfWhoseRunsItRefuses", new Form("OneC", "Count",
                "{ let m = if q < 5 then Count(q) else Count(0) \n OneC { a = m, w = q <= 3 } }"));
        // a construction over a place no rule on the way reads
        FORMS.put("overAPlaceNoRuleReads", new Form("OneC", "Count",
                "OneC { a = Count(q), w = Decimal.compare(d, e) <= 0 }"));
        FORMS.put("rightOfAnOr", new Form("OneC", "Count",
                "{ let ok = q < 0 || Count(q).value >= 3 \n OneC { a = Count(0), w = ok } }"));
        FORMS.put("armNoRunTakes", new Form("OneS", "Small",
                "if q > 5 && q < 3 then OneS { s = Small(q), w = q <= 3 } "
                        + "else OneS { s = Small(0), w = false }"));
        // two constructions: the second asking what the first did, and asking something else
        FORMS.put("twice", new Form("TwoC", "Count", "TwoC { a = Count(q), b = Count(q), "
                + "w = q <= 3 }"));
        FORMS.put("countThenSmall", new Form("CountSmall", "Count, Small",
                "CountSmall { a = Count(q), b = Small(q), w = q <= 3 }"));
        // the second refused only by values the first lets past, and only below them
        FORMS.put("countThenBig", new Form("CountBig", "Count, Big",
                "CountBig { a = Count(q), b = Big(q), w = q <= 3 }"));
        // the second asking what the first holds, and the second refusing some values the first
        // refuses first and some it lets past
        FORMS.put("countThenAboveMinusFive", new Form("CountAbove", "Count, AboveMinusFive",
                "CountAbove { a = Count(q), b = AboveMinusFive(q), w = q <= 3 }"));
        FORMS.put("countThenWithin", new Form("CountWithin", "Count, Within",
                "CountWithin { a = Count(q), b = Within(q), w = q <= 3 }"));
        // what a construction asks of one of two numbers, of a product, and of nothing
        FORMS.put("eitherOfTwo", new Form("OneH", "Held",
                "OneH { h = Held(Decimal.max(d, e)), w = Decimal.compare(d, 3.0m) <= 0 }"));
        FORMS.put("eitherOfANumberAndOne", new Form("OneH", "Held",
                "OneH { h = Held(Decimal.max(d, 1.0m)), w = Decimal.compare(d, 3.0m) <= 0 }"));
        FORMS.put("product", new Form("OneH", "Held",
                "OneH { h = Held(Decimal.multiply(d, e)), w = Decimal.compare(d, 3.0m) <= 0 }"));
        FORMS.put("aConstant", new Form("OneC", "Count", "OneC { a = Count(5), w = q <= 3 }"));
        // a construction an attempt tests, which takes the other arm where it is refused: alone,
        // before a construction asking what it would have, and before a rule below what it asks
        FORMS.put("attempted", new Form("OneC", "Count",
                "{ let n = if Count(q) as m then m else Count(0) \n OneC { a = n, w = q <= 3 } }"));
        FORMS.put("attemptedThenMade", new Form("CountFlag", "Count",
                "{ let ok = if Count(q) as m then true else false \n "
                        + "CountFlag { a = Count(q), ok = ok, w = q <= 3 } }"));
        FORMS.put("attemptedBeforeARuleBelowIt", new Form("CountFlag", "Count",
                "{ let ok = if Count(q) as m then true else false \n "
                        + "CountFlag { a = Count(0), ok = ok, w = q < -5 } }"));
        // something before it that may end a run first
        FORMS.put("overflowFirst", new Form("OneC", "Count",
                "OneC { a = Count(q + 1), w = q <= 3 }"));
        // what it is made of may end the run first, an Int worked out past its type
        NOT_SHOWN.put("overflowFirst", WhyAConstructionStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP);
        // the construction before it refuses no run, which is read as asking nothing
        FORMS.put("aConstructionThatRefusesNoneFirst", new Form("TwoH", "Held",
                "{ let f = Decimal.multiply(d, e) \n TwoH { a = Held(Decimal.max(0.0m, "
                        + "Decimal.subtract(d, f))), b = Held(Decimal.min(f, d)), "
                        + "w = Decimal.compare(d, 3.0m) <= 0 } }"));
    }

    @Test
    void aConstructionIsToldOfAStopWhereARunStopsThere() throws Exception {
        List<String> names = new ArrayList<>(FORMS.keySet());
        StringBuilder model = new StringBuilder("""
                module demo

                data In = { q: Int, d: Decimal, e: Decimal }
                data Count = Int
                    invariant value >= 0
                data Small = Int
                    invariant value <= 10
                data Big = Int
                    invariant value >= 5
                data AboveMinusFive = Int
                    invariant value >= -5
                data Within = Int
                    invariant value >= -5 && value <= 100
                data Held = Decimal
                    invariant value >= 0.0m
                data OneC = { a: Count, w: Bool }
                data TwoC = { a: Count, b: Count, w: Bool }
                data CountSmall = { a: Count, b: Small, w: Bool }
                data CountBig = { a: Count, b: Big, w: Bool }
                data CountAbove = { a: Count, b: AboveMinusFive, w: Bool }
                data CountWithin = { a: Count, b: Within, w: Bool }
                data CountFlag = { a: Count, ok: Bool, w: Bool }
                data OneS = { s: Small, w: Bool }
                data OneH = { h: Held, w: Bool }
                data TwoH = { a: Held, b: Held, w: Bool }
                """);
        for (int at = 0; at < names.size(); at++) {
            Form form = FORMS.get(names.get(at));
            String body = form.body().replaceAll("\\bq\\b", "i.q").replaceAll("\\bd\\b", "i.d")
                    .replaceAll("\\be\\b", "i.e");
            model.append("\nbehavior b").append(at).append(" : (i: In) -> ").append(form.output())
                    .append(" constructs ").append(form.output()).append(", ")
                    .append(form.constructs())
                    .append("\nlet b").append(at).append(" (i) = ").append(body).append('\n');
        }
        Compilation compilation = ACompiledModel.measured(model.toString(),
                new Adequacy.Asked(Adequacy.Level.OFF, false));
        Map<String, int[]> said = notes(compilation);
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(model.toString()),
                AConstructionIsToldOfAStopWhereARunStopsThereTest.class.getClassLoader());
        TreeSet<String> shownAndNoRunStops = new TreeSet<>();
        TreeSet<String> shownAndItsValueDoesNotStop = new TreeSet<>();
        TreeSet<String> stopsAndNotShown = new TreeSet<>();
        TreeSet<String> stopsAndNothingSaid = new TreeSet<>();
        TreeSet<String> notSaidWhy = new TreeSet<>();
        for (int at = 0; at < names.size(); at++) {
            Object behavior = Emitted.behavior(loader, "demo", "b" + at)
                    .getConstructor().newInstance();
            boolean stops = someRunStops(loader, behavior);
            int[] counts = said.getOrDefault("b" + at, new int[2]);
            if (!stops && counts[SHOWN] > 0) {
                shownAndNoRunStops.add(names.get(at));
            }
            // And the value each stop shown rests on, run: it stops, whatever the places it does
            // not name hold.
            for (AConstructionStopShown shown : constructionStopsShown(compilation, "b" + at)) {
                Map<String, Object> in = new LinkedHashMap<>(Map.of("q", 0L,
                        "d", BigDecimal.ZERO, "e", BigDecimal.ZERO));
                for (AStopShown.NumberAt number : shown.at()) {
                    String field = ((TermPath.Step.Field) number.place().steps().getLast()).name();
                    in.put(field, field.equals("q") ? (Object) number.number().longValueExact()
                            : new BigDecimal(number.number()));
                }
                PhysicalPos written = SourceRendering.namedByIdentity(compilation.texts())
                        .layouts().resolve(shown.asks().at());
                if (!stopsAt(loader, behavior, in, shown.asks().construction(), written)) {
                    shownAndItsValueDoesNotStop.add(names.get(at) + " at " + in + ", told of "
                            + shown.asks().construction() + " at " + written);
                }
            }
            if (stops && counts[SHOWN] == 0) {
                stopsAndNotShown.add(names.get(at));
                if (counts[NOT_RESOLVED] == 0) {
                    stopsAndNothingSaid.add(names.get(at));
                }
            }
            WhyAConstructionStopIsNotShown why = NOT_SHOWN.get(names.get(at));
            List<WhyAConstructionStopIsNotShown> reasons = reasonsSaid(compilation, "b" + at);
            if (why != null && !reasons.contains(why)) {
                notSaidWhy.add(names.get(at) + " said " + reasons);
            }
        }
        assertAll(
                () -> assertEquals(new TreeSet<>(), shownAndNoRunStops,
                        "told that a run stops at a construction, and no run of the inputs tried "
                                + "stops"),
                () -> assertEquals(new TreeSet<>(), shownAndItsValueDoesNotStop,
                        "told that a run stops at a construction, and the run of the value the "
                                + "stop rests on does not stop at that construction where it is "
                                + "written"),
                () -> assertEquals(new TreeSet<>(NOT_SHOWN.keySet()), stopsAndNotShown,
                        "a run stops and no stop is shown, beside the forms the compiler cannot "
                                + "yet show"),
                () -> assertEquals(new TreeSet<>(), stopsAndNothingSaid,
                        "a run stops and the report says nothing of it, not even that it is not "
                                + "resolved"),
                () -> assertEquals(new TreeSet<>(), notSaidWhy,
                        "a stop not resolved is said without the reason written down for it"));
    }

    /** Why each construction on the way to a rule of {@code behavior} is said as not resolved,
     *  of every rule the reading says it of. */
    private static List<WhyAConstructionStopIsNotShown> reasonsSaid(Compilation compilation,
                                                                     String behavior) {
        Partitions.Partitioning divided =
                compilation.db().ask(new Adequacy.Divided("demo", behavior)).value();
        List<WhyAConstructionStopIsNotShown> out = new ArrayList<>();
        for (WhatIsShownOfAStop each : divided.stopsShown()) {
            if (each instanceof RuleWhereAStopIsNotShown open) {
                open.asks().forEach(one -> out.add(one.why()));
            }
        }
        return out;
    }

    private static final int SHOWN = 0;
    private static final int NOT_RESOLVED = 1;

    private static boolean someRunStops(ClassLoader loader, Object behavior) throws Exception {
        for (long q : WHOLE) {
            for (BigDecimal d : DECIMAL) {
                for (BigDecimal e : DECIMAL) {
                    if (stopsAt(loader, behavior, Map.of("q", q, "d", d, "e", e))) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    private static boolean stopsAt(ClassLoader loader, Object behavior, Map<String, Object> raw)
            throws Exception {
        Object in = Codecs.decoded(loader, "demo.In", raw);
        try {
            Codecs.apply(behavior, in);
            return false;
        } catch (ConstraintViolation stopped) {
            return true;
        }
    }

    /** Whether the run of {@code raw} stops at the construction of {@code type} written at
     *  {@code written}, its invariant not holding: not past it, and not at anything else first,
     *  another construction of the same type included. */
    private static boolean stopsAt(ClassLoader loader, Object behavior, Map<String, Object> raw,
                                   String type, PhysicalPos written) throws Exception {
        Object in = Codecs.decoded(loader, "demo.In", raw);
        try {
            Codecs.apply(behavior, in);
            return false;
        } catch (ConstraintViolation stopped) {
            return stopped.failure() instanceof InvariantFailure failure
                    && failure.type().equals(type) && stopped.site() != null
                    && stopped.site().line() == written.line()
                    && stopped.site().column() == written.column();
        }
    }

    /** What shows a run on the way to a rule of {@code behavior} stops at a construction, of
     *  every rule the reading says it of. */
    private static List<AConstructionStopShown> constructionStopsShown(Compilation compilation,
                                                                        String behavior) {
        Partitions.Partitioning divided =
                compilation.db().ask(new Adequacy.Divided("demo", behavior)).value();
        List<AConstructionStopShown> out = new ArrayList<>();
        for (WhatIsShownOfAStop each : divided.stopsShown()) {
            if (each instanceof RuleWhereARunMayStop stops) {
                out.addAll(stops.constructions());
            }
        }
        return out;
    }

    /** How many {@code may stop a run} notes that tell a stop at a construction ({@link #SHOWN})
     *  and how many {@code stop not resolved} notes ({@link #NOT_RESOLVED}) each behavior's report
     *  holds. */
    private static Map<String, int[]> notes(Compilation compilation) {
        Pattern header = Pattern.compile("^(\\w+)\\s+implemented\\b.*");
        Map<String, int[]> out = new LinkedHashMap<>();
        String current = null;
        for (String line : AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .map(String::strip).toList()) {
            Matcher started = header.matcher(line);
            if (started.matches()) {
                current = started.group(1);
                out.put(current, new int[2]);
            } else if (current != null && line.startsWith("· may stop a run:")
                    && line.contains("stops at a construction on the way to this rule")) {
                out.get(current)[SHOWN]++;
            } else if (current != null && line.startsWith("· stop not resolved:")) {
                out.get(current)[NOT_RESOLVED]++;
            }
        }
        return out;
    }
}
