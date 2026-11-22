package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.DocumentShape;
import souther.compiler.diag.SourceRendering;
import souther.compiler.observe.Figure;
import souther.compiler.partition.Allowances;
import souther.compiler.partition.BodyReading;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.report.AdequacyReport;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.List;
import java.util.Locale;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior is left unmeasured for its author to change where a change is told and measuring it as
 * written runs into a figure, and measured where either is missing ({@link ToBeChangedFirst}).
 *
 * <p>What measuring costs is what the choices multiply to on the way down and not how many
 * applications or choices are written: each half is held by two models told alike, one of which
 * multiplies. A search of days applies its helper once to each, and where the helper compares a
 * number each day is reached past the ways every day before it fails; the same search over cases
 * of a sum applies its helper as often and draws no line. A chain of choices over the inputs is
 * read in a part for every way through it; the same chain of choices each coming out one way is
 * read in none.
 */
class ABehaviorIsLeftToBeChangedWhereAChangeIsToldAndMeasuringIsDearTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final CompositionBudget QUESTIONS =
            CompositionBudget.QUESTIONS_A_STATEMENT_IS_ASKED;

    private static final CompositionBudget READINGS =
            CompositionBudget.TOTAL_READINGS_OF_ONE_CONDITION;

    /** The questions of a statement held to a figure a search of four days runs into. */
    private static final Allowances FEW_QUESTIONS = Allowances.DECLARED.with(QUESTIONS, 8);

    /** The readings of a condition held to a figure a chain of four choices runs into. */
    private static final Allowances FEW_READINGS = Allowances.DECLARED
            .with(CompositionBudget.READINGS_OF_ONE_CONDITION, 8)
            .with(READINGS, 16);

    /** Beside the behavior that may be left, one nothing is told of, with a class no row is in. */
    private static final String BESIDE = """

            behavior beside : (flag: Bool) -> Int
            let beside (flag) = if flag then 1 else 0
            example beside
                | "on" : (true) -> 1
            """;

    /** Days searched for the first one whose number is in a range, past the ones before it. */
    private static final String SEARCHING_NUMBERS = """
            module m

            let fits (limit: Int, n: Int): Bool = n >= limit && n <= limit + 4

            let firstFit (limit: Int, from: Int): Int =
                List.rangeInclusive(0, 3)
                    |> List.map(n -> from + n)
                    |> List.find(d -> fits(limit, d))
                    |> Option.withDefault(from)

            behavior asked : (limit: Int, from: Int) -> Bool
            let asked (limit, from) = Bool.not(fits(limit, firstFit(limit, from)))
            """ + BESIDE;

    /** The same shape over the cases of a sum, which no line is drawn on. */
    private static final String SEARCHING_CASES = """
            module m

            data Room = Kitchen | Study | Garden

            let fits (wanted: Room, room: Room): Bool = wanted == room

            behavior asked : (wanted: Room) -> Bool
            let asked (wanted) =
                List.any(room -> fits(wanted, room), [ Kitchen, Study, Garden ])
            """ + BESIDE;

    /** A chain of choices, each {@code chosen} of the last and an input of its own. */
    private static String chain(String chosen) {
        return """
                module m

                let pick (a: Int, b: Int): Int = %s

                behavior asked : (n0: Int, h0: Int, h1: Int, h2: Int, h3: Int) -> Bool
                let asked (n0, h0, h1, h2, h3) = {
                    let n1 = pick(n0, h0) + 1
                    let n2 = pick(n1, h1) + 1
                    let n3 = pick(n2, h2) + 1
                    let n4 = pick(n3, h3) + 1
                    n4 == 0
                }
                """.formatted(chosen) + BESIDE;
    }

    private static final String CHOICES_THAT_MULTIPLY = chain("if a < b then a else b");

    private static final String CHOICES_THAT_COME_OUT_ONE_WAY = chain("if 1 < 2 then a else b");

    private static Compilation measured(String model, Allowances allowances, boolean leaving) {
        Compilation compilation = Compilation.ofSource(model, "Main").allowing(allowances);
        compilation.measure(Adequacy.Asked.fullReport());
        if (leaving) {
            compilation.leaveWhatIsToBeChanged();
        }
        return ACompiledModel.compiles(compilation);
    }

    private static ToBeChangedFirst.Left left(String model, Allowances allowances) {
        return Adequacy.leftToBeChanged(measured(model, allowances, true).db(), "m", "asked");
    }

    private static Optional<String> figure(ToBeChangedFirst.Left left) {
        return left.figure().map(Figure::name);
    }

    @Test
    void aSearchOfNumbersIsLeftAndTheSameSearchOverTheCasesOfASumIsMeasured() {
        assertEquals(Optional.of(QUESTIONS.name()),
                figure(left(SEARCHING_NUMBERS, FEW_QUESTIONS)));

        Compilation cases = measured(SEARCHING_CASES, FEW_QUESTIONS, true);
        assertFalse(cases.db().ask(new HelpersReadOnApplicationsAroundThem("m", "asked")).value()
                .isEmpty(), "the same change is told of the search over cases");
        assertEquals(Optional.empty(), figure(Adequacy.leftToBeChanged(cases.db(), "m", "asked")));
    }

    @Test
    void aChainOfChoicesIsLeftAndTheSameChainOfChoicesThatComeOutOneWayIsMeasured() {
        assertEquals(Optional.of(READINGS.name()),
                figure(left(CHOICES_THAT_MULTIPLY, FEW_READINGS)));

        Compilation oneWay = measured(CHOICES_THAT_COME_OUT_ONE_WAY, FEW_READINGS, true);
        assertTrue(oneWay.db().ask(new ConditionsReadThroughTooManyChoices("m", "asked")).value()
                .conditions() > 0, "the same change is told of the chain that comes out one way");
        assertEquals(Optional.empty(),
                figure(Adequacy.leftToBeChanged(oneWay.db(), "m", "asked")));
    }

    /** Dear and told of nothing: waiting is the only way to what its rows do not cover. */
    @Test
    void aBehaviorNoChangeIsToldOfIsMeasuredHoweverDear() {
        Compilation compilation = measured("""
                module m
                behavior asked : (a: Int, b: Int, c: Int) -> Bool
                let asked (a, b, c) = a >= 1 && b >= 2 && c >= 3 && a + b >= 4
                """, Allowances.DECLARED.with(QUESTIONS, 0), true);

        assertTrue(compilation.db().ask(new Adequacy.WhatStopsMeasuring("m", "asked")).value()
                .isPresent(), "measuring it runs into the figure");
        assertEquals(ToBeChangedFirst.Left.NOTHING,
                Adequacy.leftToBeChanged(compilation.db(), "m", "asked"));
    }

    /** Told and within the figures, which is what the figures declared make of this model. */
    @Test
    void aBehaviorWithinTheFiguresIsMeasuredAsItIsWhereNothingIsLeft() {
        assertEquals(ToBeChangedFirst.Left.NOTHING, left(SEARCHING_NUMBERS, Allowances.DECLARED));
        Compilation leaving = measured(SEARCHING_NUMBERS, Allowances.DECLARED, true);
        Compilation measuring = measured(SEARCHING_NUMBERS, Allowances.DECLARED, false);

        assertEquals(page(measuring, Locale.ENGLISH), page(leaving, Locale.ENGLISH));
    }

    @Test
    void whereTheBuildDoesNotAskForItEveryBehaviorIsMeasured() {
        Compilation compilation = measured(SEARCHING_NUMBERS, FEW_QUESTIONS, false);

        assertEquals(ToBeChangedFirst.Left.NOTHING,
                Adequacy.leftToBeChanged(compilation.db(), "m", "asked"));
        assertEquals(List.of(), AdequacyReport.of(compilation).leftToBeChanged());
    }

    /** The body of the behavior is read by no measure, and the other behavior is measured as it
     *  is where nothing is left. */
    @Test
    void theBodyIsReadByNoMeasureAndTheOtherBehaviorsAreMeasured() {
        Compilation leaving = measured(SEARCHING_NUMBERS, FEW_QUESTIONS, true);
        Db db = leaving.db();
        Bodies.Elaborated checked = db.ask(new Bodies.Observable("m")).value();

        assertInstanceOf(BodyReading.ToBeChangedFirst.class,
                Adequacy.bodyReading(db, "m", checked, "asked"));
        assertInstanceOf(BodyReading.Read.class,
                Adequacy.bodyReading(db, "m", checked, "beside"));
        assertFalse(db.ask(new Adequacy.DecisionReadings("m")).value().containsKey("asked"));
        assertFalse(db.ask(new Adequacy.PathReached("m")).value().containsKey("asked"));
        assertFalse(db.ask(new Adequacy.Meets("m")).value().containsKey("asked"));

        Compilation measuring = measured(SEARCHING_NUMBERS, FEW_QUESTIONS, false);
        assertEquals(page(only(measuring, "beside"), measuring, Locale.ENGLISH),
                page(only(leaving, "beside"), leaving, Locale.ENGLISH));
    }

    @Test
    void theReportSaysWhatToChangeInTheDocumentAndInBothLanguages() {
        Compilation compilation = measured(SEARCHING_NUMBERS, FEW_QUESTIONS, true);
        AdequacyReport report = AdequacyReport.of(compilation);

        assertEquals(List.of("m.asked"), report.leftToBeChanged());
        JsonNode document = JSON.readTree(
                report.json(SourceRendering.namedByIdentity(compilation.texts())));
        DocumentShape.assertShapedLikeTheSchema(document);
        JsonNode asked = behavior(document, "asked");
        JsonNode told = asked.get("toBeChangedFirst");
        assertEquals(1, told.get("figures").size(), told.toString());
        assertEquals("m.fits",
                told.get("helpersAppliedToEachElement").get(0).get("helper").asString());
        assertEquals(List.of("m.firstFit"), JSON.convertValue(
                told.get("helpersAppliedToEachElement").get(0).get("calledInside"), List.class));
        assertEquals("behavior_to_be_changed_first", asked.get("weakening").get(0).asString());
        assertNull(behavior(document, "beside").get("toBeChangedFirst"));

        String english = page(compilation, Locale.ENGLISH);
        assertTrue(english.contains("not measured: as it is written, measuring it stops at"),
                english);
        assertTrue(english.contains("Declared as a behavior, `fits` reads them once"), english);
        String japanese = page(compilation, Locale.JAPANESE);
        assertTrue(japanese.contains("測っていない: 今の書き方のまま測ると、途中で上限に達する"), japanese);
        assertTrue(japanese.contains("`fits` を behavior として宣言すると"), japanese);
    }

    /** Nothing was shown of its rows: the verdict over it alone is open, and not a gap. */
    @Test
    void theVerdictOverItIsOpen() {
        Compilation compilation = measured(SEARCHING_NUMBERS, FEW_QUESTIONS, true);

        assertEquals(AdequacyReport.AdequacyStatus.UNDETERMINED,
                only(compilation, "asked").adequacy());
    }

    /** What is told is what makes it cheap: changed as told, the model has nothing left. */
    @Test
    void changedAsToldNothingIsLeft() {
        ToBeChangedFirst.Left left = left("""
                module m

                behavior fits : (limit: Int, n: Int) -> Bool
                let fits (limit, n) = n >= limit && n <= limit + 4

                behavior asked : (limit: Int, from: Int) -> Bool
                let asked (limit, from) =
                    Bool.not(fits(limit, List.rangeInclusive(0, 3)
                        |> List.map(n -> from + n)
                        |> List.find(d -> fits(limit, d))
                        |> Option.withDefault(from)))
                """ + BESIDE, FEW_QUESTIONS);

        assertEquals(ToBeChangedFirst.Left.NOTHING, left);
    }

    private static JsonNode behavior(JsonNode document, String name) {
        for (JsonNode each : document.get("modules").get(0).get("behaviors")) {
            if (each.get("name").asString().equals(name)) {
                return each;
            }
        }
        throw new AssertionError("no behavior " + name);
    }

    private static AdequacyReport only(Compilation compilation, String behavior) {
        return AdequacyReport.of(compilation).only(null, behavior);
    }

    private static String page(Compilation compilation, Locale locale) {
        return page(AdequacyReport.of(compilation), compilation, locale);
    }

    private static String page(AdequacyReport report, Compilation compilation, Locale locale) {
        return report.human(SourceRendering.namedByIdentity(compilation.texts()), locale);
    }
}
