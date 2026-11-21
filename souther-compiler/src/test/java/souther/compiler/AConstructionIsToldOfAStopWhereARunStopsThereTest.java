package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.PhysicalPos;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.AConstructionStopNotShown;
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
import souther.runtime.ConstraintViolation;
import souther.runtime.InvariantFailure;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertAll;
import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A run on the way to a rule is told to stop at a construction only where some run does stop, and
 * a run that stops is never left unsaid.
 *
 * <p>The truth is the program run: each behavior is compiled and run on every input of a small
 * grid, and a run that stops is a {@code ConstraintViolation}. What the findings of each behavior
 * say, which are what its report is written from, is held to that and not to what the reading of
 * the constructions came to, so a stop they tell where no run stops, or one they say nothing of, is
 * found by the program. How the report words a finding is held elsewhere.
 *
 * <p>Held construction by construction, each by the type made and where it is written, which is
 * what a run that stops there says: a stop shown at one construction of a behavior says nothing
 * of another, and a construction the reading leaves out is found even beside one it tells.
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
        // one on an arm beside one every run makes, both stopped at by some run: a stop shown of
        // the one says nothing of the other
        FORMS.put("anArmBesideEveryRun", new Form("TwoC", "Count",
                "{ let m = if Decimal.compare(d, 0.0m) < 0 then Count(q) else Count(0) \n "
                        + "TwoC { a = m, b = Count(q), w = q <= 3 } }"));
        // one in a function bound by a name, before the rule the function holds, which the one
        // call applying it applies once
        FORMS.put("inANamedFunction", new Form("OneC", "Count",
                "{ let f = x -> { let n = Count(x) \n n.value <= 3 } \n "
                        + "OneC { a = Count(0), w = List.all(f, [q]) } }"));
        // the same applied to two elements, the second application coming after the first ran
        // the body whole, so no run is shown to get to it first
        FORMS.put("inANamedFunctionAppliedTwice", new Form("OneC", "Count",
                "{ let f = x -> { let n = Count(x) \n n.value <= 3 } \n "
                        + "OneC { a = Count(0), w = List.all(f, [q, q]) } }"));
        NOT_SHOWN.put("inANamedFunctionAppliedTwice",
                WhyAConstructionStopIsNotShown.REACH_NOT_SHOWN);
        // one before a function bound by a name, on the way to the rule the function holds where
        // the call applying it is
        FORMS.put("beforeANamedFunction", new Form("OneC", "Count",
                "{ let m = Count(q) \n let f = x -> x <= 3 \n "
                        + "OneC { a = m, w = List.all(f, [q]) } }"));
        // one in what a call applying a function bound by a name is handed, worked out before
        // the call applies it
        FORMS.put("inWhatTheCallIsHanded", new Form("OneC", "Count",
                "{ let f = x -> x <= 3 \n OneC { a = Count(0), w = List.all(f, [Count(q).value]) } }"));
        // the same function applied by two calls, and a construction between them, which only a
        // run on the way to the rule by the second call gets to first
        FORMS.put("beforeTwoCallsOfANamedFunction", new Form("OneC", "Count",
                "{ let m = Count(q) \n let f = x -> x <= 3 \n "
                        + "OneC { a = m, w = List.all(f, [q]) && List.any(f, [q]) } }"));
        FORMS.put("betweenTwoCallsOfANamedFunction", new Form("CountFlag", "Count",
                "{ let f = x -> x <= 3 \n let ok = List.all(f, [q]) \n let m = Count(q) \n "
                        + "CountFlag { a = m, ok = ok, w = List.any(f, [q]) } }"));
        // the first call, worked out before it by a run on the way by the second, applies a body
        // the call does not hold, which may end the run for all that is read of it
        NOT_SHOWN.put("betweenTwoCallsOfANamedFunction",
                WhyAConstructionStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP);
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
        BytesClassLoader loader = new BytesClassLoader(compilation.classes(),
                AConstructionIsToldOfAStopWhereARunStopsThereTest.class.getClassLoader());
        SourceRendering rendering = SourceRendering.namedByIdentity(compilation.texts());
        TreeSet<String> shownAndNoRunStops = new TreeSet<>();
        TreeSet<String> shownAndItsValueDoesNotStop = new TreeSet<>();
        TreeSet<String> stopsAndNotShown = new TreeSet<>();
        TreeSet<String> stopsAndNothingSaid = new TreeSet<>();
        TreeSet<String> notSaidWhy = new TreeSet<>();
        for (int at = 0; at < names.size(); at++) {
            String name = names.get(at);
            Object behavior = Emitted.behavior(loader, "demo", "b" + at)
                    .getConstructor().newInstance();
            Set<String> stopsAt = constructionsSomeRunStopsAt(loader, behavior);
            Said said = said(compilation, "b" + at, rendering);
            for (String site : said.shownAt()) {
                if (!stopsAt.contains(site)) {
                    shownAndNoRunStops.add(name + ": " + site);
                }
            }
            // And the value each stop shown rests on, run: it stops, whatever the places it does
            // not name hold.
            for (AConstructionStopShown shown : said.shown()) {
                Map<String, Object> in = new LinkedHashMap<>(Map.of("q", 0L,
                        "d", BigDecimal.ZERO, "e", BigDecimal.ZERO));
                for (AStopShown.NumberAt number : shown.at()) {
                    String field = ((TermPath.Step.Field) number.place().steps().getLast()).name();
                    in.put(field, field.equals("q") ? (Object) number.number().longValueExact()
                            : new BigDecimal(number.number()));
                }
                String site = siteOf(shown.asks().construction(), shown.asks().at(), rendering);
                if (!site.equals(constructionStoppedAt(loader, behavior, in))) {
                    shownAndItsValueDoesNotStop.add(name + " at " + in + ", told of " + site);
                }
            }
            // And each construction some run stops at, by where it is written: a stop shown of
            // one construction says nothing of another.
            for (String site : stopsAt) {
                if (said.shownAt().contains(site)) {
                    continue;
                }
                stopsAndNotShown.add(name);
                List<WhyAConstructionStopIsNotShown> why = said.notShownAt().get(site);
                if (why == null) {
                    stopsAndNothingSaid.add(name + ": " + site);
                } else if (NOT_SHOWN.containsKey(name) && !why.contains(NOT_SHOWN.get(name))) {
                    notSaidWhy.add(name + ": " + site + " said " + why);
                }
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

    /**
     * What the findings of one behavior say of a run stopping at a construction on its way to its
     * rules, which is what its report writes from, each construction by where it is written
     * ({@link #siteOf}).
     *
     * @param shown      what shows a run on the way stops at a construction, of every rule
     * @param shownAt    where each of {@code shown} is written
     * @param notShownAt each construction said not resolved, with why, of every rule
     */
    private record Said(List<AConstructionStopShown> shown, Set<String> shownAt,
                        Map<String, List<WhyAConstructionStopIsNotShown>> notShownAt) {}

    private static Said said(Compilation compilation, String behavior,
                             SourceRendering rendering) {
        Partitions.Partitioning divided =
                compilation.db().ask(new Adequacy.Divided("demo", behavior)).value();
        List<AConstructionStopShown> shown = new ArrayList<>();
        Set<String> shownAt = new TreeSet<>();
        Map<String, List<WhyAConstructionStopIsNotShown>> notShownAt = new TreeMap<>();
        for (WhatIsShownOfAStop each : divided.stopsShown()) {
            if (each instanceof RuleWhereARunMayStop stops) {
                for (AConstructionStopShown one : stops.constructions()) {
                    shown.add(one);
                    shownAt.add(siteOf(one.asks().construction(), one.asks().at(), rendering));
                }
            } else if (each instanceof RuleWhereAStopIsNotShown open) {
                for (AConstructionStopNotShown one : open.asks()) {
                    notShownAt.computeIfAbsent(siteOf(one.construction(), one.at(), rendering),
                            _ -> new ArrayList<>()).add(one.why());
                }
            }
        }
        return new Said(shown, shownAt, notShownAt);
    }

    /** A construction as the type made and the line and column it is written at, which is what a
     *  run that stops there says of where it stopped. */
    private static String siteOf(String type, SourcePos at, SourceRendering rendering) {
        PhysicalPos written = rendering.layouts().resolve(at);
        return type + " at " + written.line() + ":" + written.column();
    }

    /** Every construction some run of the grid stops at ({@link #constructionStoppedAt}). */
    private static Set<String> constructionsSomeRunStopsAt(ClassLoader loader, Object behavior)
            throws Exception {
        Set<String> out = new TreeSet<>();
        for (long q : WHOLE) {
            for (BigDecimal d : DECIMAL) {
                for (BigDecimal e : DECIMAL) {
                    String site = constructionStoppedAt(loader, behavior,
                            Map.of("q", q, "d", d, "e", e));
                    if (site != null) {
                        out.add(site);
                    }
                }
            }
        }
        return out;
    }

    /** The construction the run of {@code raw} stops at, its invariant not holding, as
     *  {@link #siteOf} writes it: null where it stops at nothing, or at something else. */
    private static String constructionStoppedAt(ClassLoader loader, Object behavior,
                                                Map<String, Object> raw) throws Exception {
        Object in = Codecs.decoded(loader, "demo.In", raw);
        try {
            Codecs.apply(behavior, in);
            return null;
        } catch (ConstraintViolation stopped) {
            return stopped.failure() instanceof InvariantFailure failure && stopped.site() != null
                    ? failure.type() + " at " + stopped.site().line() + ":"
                            + stopped.site().column()
                    : null;
        }
    }

}
