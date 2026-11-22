package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.DocumentShape;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.AComparisonRead;
import souther.compiler.partition.Allowances;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.report.AdequacyReport;
import souther.compiler.types.ValueName;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A condition read no further at a figure of this compiler is told of with what an author
 * declares as a behavior so that it is read, and the model changed so is one nothing stops in.
 *
 * <p>What a behavior answers is one value to its caller, so a helper whose choices multiply the
 * readings of a condition leaves none of them once it is a behavior
 * ({@link WhatToDeclare}). Where no helper accounts for it, the condition is what is written in a
 * behavior. Each is held to the model it names: declared as told, the model has no condition that
 * stopped.
 */
class AConditionStoppedAtAFigureIsToldWithWhatToDeclareTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String WRITTEN_IN_A_BEHAVIOR = "what is to be written in a behavior is"
            + " the condition: handed what it compares, the behavior reads it once, over its own"
            + " inputs";

    /** The readings of a condition held to a figure a short model reaches. */
    private static final Allowances HELD = Allowances.DECLARED
            .with(CompositionBudget.READINGS_OF_ONE_CONDITION, 8)
            .with(CompositionBudget.TOTAL_READINGS_OF_ONE_CONDITION, 16);

    /** How many choices the value compared is made through, one after another. */
    private static final int CHOICES = 4;

    /** More elements than are read on one by one. */
    private static final String LONG_TABLE = IntStream.rangeClosed(1, 10)
            .mapToObj(String::valueOf).collect(Collectors.joining(", "));

    /** A comparison of a value made by {@code chosen} again and again, each from the last. */
    private static String comparedAfter(String declared, String chosen) {
        String inputs = IntStream.range(0, CHOICES).mapToObj(i -> ", h" + i)
                .collect(Collectors.joining());
        String steps = IntStream.range(0, CHOICES)
                .mapToObj(i -> "    let n" + (i + 1) + " = "
                        + chosen.formatted("n" + i, "h" + i) + " + 1\n")
                .collect(Collectors.joining());
        return "module m\n\n" + declared + "\nbehavior paid : (n0: Int"
                + inputs.replaceAll("(h\\d)", "$1: Int") + ") -> Bool\nlet paid (n0" + inputs
                + ") = {\n" + steps + "    n" + CHOICES + " == 0\n}\n";
    }

    private static Compilation measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main").allowing(HELD);
        compilation.measure(new Adequacy.Asked(Adequacy.Level.OFF, false));
        return ACompiledModel.compiles(compilation);
    }

    private static WhatToDeclare told(Compilation compilation) {
        return compilation.db().ask(new ConditionsReadThroughTooManyChoices("m", "paid")).value();
    }

    private static ConditionsStoppedAtAFigure.Stopped stoppedIn(Compilation compilation,
                                                                String behavior) {
        return compilation.db().ask(new ConditionsStoppedAtAFigure("m", behavior)).value();
    }

    private static int stopped(Compilation compilation, String behavior) {
        return stoppedIn(compilation, behavior).conditions();
    }

    private static String page(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static JsonNode document(Compilation compilation) throws Exception {
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
    }

    @Test
    void theHelperWhoseChoicesMultiplyIsNamedOnThePageAndInTheDocument() throws Exception {
        Compilation compilation = measured(comparedAfter(
                "let smaller (a: Int, b: Int): Int = if a < b then a else b\n",
                "smaller(%s, %s)"));
        assertTrue(stopped(compilation, "paid") > 0, "the model stops a condition at a figure");

        WhatToDeclare told = told(compilation);
        assertEquals(List.of("smaller"),
                told.helpers().stream().map(each -> each.helper().name()).toList());
        assertEquals(CHOICES, told.helpers().getFirst().calls());
        assertEquals(List.of(), told.helpers().getFirst().calledInside());
        assertEquals(0, told.inABehavior());

        Compilation small = measured(SMALL);
        AdequacyReport report = saying(small, stoppedIn(compilation, "paid"));
        SourceRendering rendering = SourceRendering.namedByIdentity(small.texts());
        String page = report.humanInEnglish(rendering);
        assertTrue(page.contains("conditions read no further: " + stopped(compilation, "paid")
                + ", stopped at"), page);
        assertTrue(page.contains("Declared as a behavior, `smaller` is not expanded here and"
                + " counts as one answer"), page);
        assertFalse(page.contains(WRITTEN_IN_A_BEHAVIOR), page);

        JsonNode document = JSON.readTree(report.json(rendering));
        DocumentShape.assertShapedLikeTheSchema(document);
        JsonNode said = document.get("modules").get(0).get("behaviors").get(0)
                .get("conditionsStoppedAtAFigure");
        assertEquals(stopped(compilation, "paid"), said.get("conditions").asInt());
        assertEquals("m.smaller", said.get("helpersToDeclare").get(0).get("helper").asString());
    }

    /** A model measured at once, which what a costly one is told of is put into the report of:
     *  what is said of it is a function of what is told, and measuring the costly one is not. */
    private static final String SMALL = """
            module m

            behavior paid : (n: Int) -> Int
            let paid (n) = n
            """;

    /** The report of {@code small}, its one behavior told {@code stopped} of. */
    private static AdequacyReport saying(Compilation small,
                                         ConditionsStoppedAtAFigure.Stopped stopped) {
        AdequacyReport real = AdequacyReport.of(small);
        AdequacyReport.ModuleReport module = real.modules().getFirst();
        AdequacyReport.BehaviorReport b = module.behaviors().getFirst();
        return new AdequacyReport(real.schemaVersion(), real.compilerVersion(),
                real.weakenedBy(), List.of(new AdequacyReport.ModuleReport(module.module(),
                        module.declaredIn(), List.of(new AdequacyReport.BehaviorReport(b.name(),
                                b.implementation(), b.evidence(), b.rowsOwed(), b.claimed(),
                                b.reported(), b.armPlaces(), b.conditionPlaces(),
                                b.rulePlaces(), b.partPlaces(), b.ruleReadings(),
                                b.ruleSettlements(), b.reachShownWrong(),
                                b.combinationReadings(), b.unobserved(), b.rowPlaces(),
                                b.weights(), b.rewritePlaces(), b.wayStops(),
                                b.helpersCalledOnEachElement(), stopped)),
                        module.declarations(), module.owedByDeclarations(), module.apart())));
    }

    @Test
    void declaredAsToldNothingStops() throws Exception {
        Compilation compilation = measured(comparedAfter("""
                behavior smaller : (a: Int, b: Int) -> Int
                let smaller (a, b) = if a < b then a else b
                """, "smaller(%s, %s)"));

        assertEquals(0, stopped(compilation, "paid"));
        assertEquals(0, stopped(compilation, "smaller"));
        assertEquals(WhatToDeclare.NOTHING, told(compilation));
        assertFalse(page(compilation).contains("read no further"));
        document(compilation).get("modules").get(0).get("behaviors").forEach(each ->
                assertNull(each.get("conditionsStoppedAtAFigure")));
    }

    /** The choices are written in the body beside the condition: no helper is named, and what is
     *  written in a behavior is the condition. */
    @Test
    void whereTheChoicesAreWrittenBesideTheConditionTheConditionIsWhatMoves() {
        Compilation compilation = measured(comparedAfter("",
                "(if %1$s < %2$s then %1$s else %2$s)"));
        assertTrue(stopped(compilation, "paid") > 0, "the model stops a condition at a figure");

        WhatToDeclare told = told(compilation);

        assertEquals(List.of(), told.helpers());
        assertEquals(told.conditions(), told.inABehavior());
        ConditionsStoppedAtAFigure.Stopped stopped = stoppedIn(compilation, "paid");
        assertEquals(stopped.conditions(), stopped.declare().inABehavior());
        Compilation small = measured(SMALL);
        String page = saying(small, stopped)
                .humanInEnglish(SourceRendering.namedByIdentity(small.texts()));
        assertTrue(page.contains("In " + stopped.conditions() + " of them, "
                + WRITTEN_IN_A_BEHAVIOR), page);
    }

    /** One condition is made through too many choices and is read whole, since no run takes an arm
     *  of any; another stops on a long table. What is declared is told of the one that stopped, and
     *  the helper of the other is told of before the reading alone. */
    @Test
    void aConditionReadWholeSuggestsNothingForOneThatStopped() {
        String steps = IntStream.range(0, CHOICES)
                .mapToObj(i -> "    let n" + (i + 1) + " = kept(n" + i + ")\n")
                .collect(Collectors.joining());
        Compilation compilation = measured("""
                module m

                let kept (n: Int): Int = if 1 < 2 then n else 0

                behavior paid : (n0: Int, m: Int) -> Bool
                let paid (n0, m) = {
                """ + steps + "    if n" + CHOICES + " == 0 then true"
                + " else List.any((x) -> x == n0 && x + m >= 10, [" + LONG_TABLE + "])\n}\n");

        assertEquals(List.of("kept"), told(compilation).helpers().stream()
                .map(each -> each.helper().name()).toList());
        ConditionsStoppedAtAFigure.Stopped stopped = stoppedIn(compilation, "paid");
        assertTrue(stopped.conditions() > 0, "the model stops a condition at a figure");
        assertEquals(List.of(), stopped.declare().helpers());
        assertEquals(stopped.conditions(), stopped.declare().inABehavior());
    }

    /** The calls are written in a helper, which cannot call a behavior: the helper around them is
     *  named beside the one to declare. */
    @Test
    void theHelpersTheCallsAreWrittenInsideAreNamed() {
        Compilation compilation = measured("""
                module m

                let smaller (a: Int, b: Int): Int = if a < b then a else b

                let smallest (a: Int, b: Int, c: Int): Int = {
                    let first = smaller(a, b)
                    if first < c then first else c
                }

                behavior paid : (a: Int, b: Int, c: Int) -> Bool
                let paid (a, b, c) = smallest(a, b, c) == 0
                """);
        // The choices the conditions of the model are made through, taken to be made through as
        // many of them as are past the readings: which helper they are in is the model's.
        List<AComparisonRead> read = compilation.db()
                .ask(new Adequacy.ComparisonsRead("m", "paid")).value().stream()
                .map(each -> new AComparisonRead(each.copy(), each.on(),
                        Collections.nCopies(7, each.through()).stream().flatMap(List::stream)
                                .toList()))
                .toList();

        List<WhatToDeclare.HelperToDeclare> helpers =
                ConditionsReadThroughTooManyChoices.told(read).helpers();

        // The comparison of the body is read through `smallest`, called in the body itself; the
        // one inside `smallest` through `smaller`, called there.
        assertEquals(List.of("smallest inside []", "smaller inside [smallest]"), helpers.stream()
                .map(each -> each.helper().name() + " inside " + each.calledInside().stream()
                        .map(ValueName.Helper::name).toList()).sorted(Comparator.reverseOrder())
                .toList());
    }

    /** A condition read on more elements written out than are read on, through no choice: told
     *  with the same, and written as told it is read. */
    @Test
    void aConditionOnEachElementOfALongTableIsToldToBeWrittenInABehavior() {
        String body = """
                behavior paid : (n: Int, m: Int) -> Bool
                let paid (n, m) = List.any((x) -> %s, [%s])
                """;
        Compilation inTheBody = measured("module m\n\n"
                + body.formatted("x == n && x + m >= 10", LONG_TABLE));
        Compilation inABehavior = measured("""
                module m

                behavior matches : (x: Int, n: Int, m: Int) -> Bool
                let matches (x, n, m) = x == n && x + m >= 10

                """ + body.formatted("matches(x, n, m)", LONG_TABLE));

        assertTrue(stopped(inTheBody, "paid") > 0, "the model stops a condition at a figure");
        assertTrue(page(inTheBody).contains(WRITTEN_IN_A_BEHAVIOR), page(inTheBody));
        assertEquals(0, stopped(inABehavior, "paid"));
        assertEquals(0, stopped(inABehavior, "matches"));
    }
}
