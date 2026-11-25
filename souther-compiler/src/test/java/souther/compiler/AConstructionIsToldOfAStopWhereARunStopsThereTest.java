package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.WhatIsShownOfAStop;
import souther.compiler.inputs.WhyAConstructionStopIsNotShown;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A run on the way to a rule is told to stop at a construction only where some run does stop, and
 * a run that stops is never left unsaid, as {@link StopsHeldToTheRuns} holds what is said of where
 * a run stops to the runs of a grid.
 *
 * <p>Held construction by construction, each by where it is written, which is what a run that stops
 * there says: a stop shown at one construction of a behavior says nothing of another, and a
 * construction the reading leaves out is found even beside one it tells. What is worked out on the
 * way to a construction is held alike, operation by operation.
 *
 * <p>The report is asked with no rows composed or run ({@link Adequacy.Level#OFF}), so a stop it
 * tells is one shown from the model and not one a row came to.
 *
 * <p>What stops a run and is said as not resolved, rather than as a stop, is written down in
 * {@link #NOT_SHOWN}, one form each with the reasons the findings give: a stop the compiler learns
 * to show moves the form out of it.
 *
 * <p>This holds the report and the program to one another on these inputs, and not on every
 * input: a stop only some other value reaches is not found by it.
 */
class AConstructionIsToldOfAStopWhereARunStopsThereTest {

    /** The input every form takes, and the values each of its places takes. */
    private static final StopsHeldToTheRuns.Input INPUT = new StopsHeldToTheRuns.Input("demo", "In",
            Map.of("q", List.of(0L, -1L, 1L, 11L, Long.MAX_VALUE, Long.MIN_VALUE),
                    "d", List.of(BigDecimal.ZERO, BigDecimal.ONE.negate(), BigDecimal.ONE),
                    "e", List.of(BigDecimal.ZERO, BigDecimal.ONE.negate(), BigDecimal.ONE)));

    /** A behavior: what it makes, the types it constructs beside that, and its body over
     *  {@code q}, {@code d} and {@code e}. */
    private record Form(String output, String constructs, String body) {}

    private static final Map<String, Form> FORMS = new LinkedHashMap<>();

    /** What a run stops at and is said as not resolved, each with the reasons said of the steps
     *  on the way it stops at. */
    private static final Map<String, Set<Enum<?>>> NOT_SHOWN = new LinkedHashMap<>();

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
                Set.of(WhyAConstructionStopIsNotShown.REACH_NOT_SHOWN));
        // the same written at one call, which a closure around it makes on each of two elements:
        // what the construction asks is read in the names of each application, and a run gets
        // to the second past the first, whose body is worked out in its own names, which what a
        // construction asks of what comes before it is not read in
        FORMS.put("inANamedFunctionAtOneCallMadeTwice", new Form("OneC", "Count",
                "{ let p: (Int) -> Bool = x -> { let ok = x <= 3 \n let later = Count(x) \n "
                        + "ok && later.value >= 0 } \n "
                        + "OneC { a = Count(0), w = List.all(y -> List.all(p, [y]), [q, q]) } }"));
        NOT_SHOWN.put("inANamedFunctionAtOneCallMadeTwice",
                Set.of(WhyAConstructionStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP));
        // one before a function bound by a name, on the way to the rule the function holds where
        // the call applying it is
        FORMS.put("beforeANamedFunction", new Form("OneC", "Count",
                "{ let m = Count(q) \n let f = x -> x <= 3 \n "
                        + "OneC { a = m, w = List.all(f, [q]) } }"));
        // one in what a call applying a function bound by a name is handed, worked out before
        // the call applies it
        FORMS.put("inWhatTheCallIsHanded", new Form("OneC", "Count",
                "{ let f = x -> x <= 3 \n OneC { a = Count(0), w = List.all(f, [Count(q).value]) } }"));
        // the same function applied by two calls, and a construction before them, which every
        // run works out before either call applies the function
        FORMS.put("beforeTwoCallsOfANamedFunction", new Form("OneC", "Count",
                "{ let m = Count(q) \n let f = x -> x <= 3 \n "
                        + "OneC { a = m, w = List.all(f, [q]) && List.any(f, [q]) } }"));
        FORMS.put("betweenTwoCallsOfANamedFunction", new Form("CountFlag", "Count",
                "{ let f = x -> x <= 3 \n let ok = List.all(f, [q]) \n let m = Count(q) \n "
                        + "CountFlag { a = m, ok = ok, w = List.any(f, [q]) } }"));
        // the first call, worked out before it by a run on the way by the second, applies a body
        // the call does not hold, which may end the run for all that is read of it
        NOT_SHOWN.put("betweenTwoCallsOfANamedFunction",
                Set.of(WhyAConstructionStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP));
        // the same with the second call made only where the first came out false: a run on the
        // way by it stops at the construction for no value that comes out so, and one that stops
        // there got to the rule by the first call already
        FORMS.put("betweenTwoCallsTheSecondOnSomeRuns", new Form("CountFlag", "Count",
                "{ let f = x -> x <= 3 \n let ok = List.all(f, [q]) \n let m = Count(q) \n "
                        + "CountFlag { a = m, ok = ok, w = ok || List.any(f, [q]) } }"));
        NOT_SHOWN.put("betweenTwoCallsTheSecondOnSomeRuns",
                Set.of(WhyAConstructionStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP));
        // one after a value is built whose template ends every run, before the rule
        FORMS.put("afterAValueThatStops", new Form("OneC", "Count",
                "{ let t = past \n let m = Count(q) \n OneC { a = m, w = q <= t } }"));
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
        NOT_SHOWN.put("overflowFirst",
                Set.of(WhyAConstructionStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP));
        // the construction before it refuses no run, which is read as asking nothing
        FORMS.put("aConstructionThatRefusesNoneFirst", new Form("TwoH", "Held",
                "{ let f = Decimal.multiply(d, e) \n TwoH { a = Held(Decimal.max(0.0m, "
                        + "Decimal.subtract(d, f))), b = Held(Decimal.min(f, d)), "
                        + "w = Decimal.compare(d, 3.0m) <= 0 } }"));
    }

    @Test
    void aConstructionIsToldOfAStopWhereARunStopsThere() {
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

                let past: Int = Int.abs(9223372036854775807) + 1
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
        ClassLoader loader = compilation.loaderSayingWhereRunsStop("demo").orElseThrow(
                () -> new AssertionError("the module is generated to say where runs stop"));
        Map<String, Object> wrong = new TreeMap<>();
        Map<String, Set<Enum<?>>> notShown = new TreeMap<>();
        for (int at = 0; at < names.size(); at++) {
            List<WhatIsShownOfAStop> said = StopsHeldToTheRuns.saidOf(compilation, "demo", "b" + at);
            StopsHeldToTheRuns.Held held = StopsHeldToTheRuns.heldTo(said,
                    new StopsHeldToTheRuns.Runs(compilation, loader, INPUT, "b" + at, said));
            if (!held.unheld().isEmpty() || !held.notHeldTo().isEmpty()) {
                wrong.put(names.get(at), List.of(held.unheld(), held.notHeldTo()));
            }
            if (!held.notShown().isEmpty()) {
                notShown.put(names.get(at), held.notShownBecause());
            }
        }
        assertEquals(Map.of(), wrong, "what is said of a step is what the runs of the grid do there");
        assertEquals(new TreeMap<>(NOT_SHOWN), notShown,
                "a run stops at a step said not resolved, for the reasons written down");
    }
}
