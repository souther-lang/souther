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
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior is left unmeasured for its author to change where a change is told and measuring it as
 * written runs into a figure, and measured where either is missing ({@link ToBeChangedFirst}).
 *
 * <p>What measuring costs is what the choices multiply to on the way down and not how many
 * applications or choices are written: each half is held by two models told alike, one of which
 * multiplies. A helper comparing a number, applied to two of them, draws a line decided in more
 * cases than one; the same over the cases of a sum draws none. A chain of choices over the inputs
 * is read once for every way through it; the same chain of choices each coming out one way is not.
 *
 * <p>Asked of the questions and not of a measurement: none is made but by the one test of the
 * report, of a behavior left.
 */
class ABehaviorIsLeftToBeChangedWhereAChangeIsToldAndMeasuringIsDearTest {

    private static final CompositionBudget QUESTIONS =
            CompositionBudget.QUESTIONS_A_STATEMENT_IS_ASKED;

    private static final CompositionBudget READINGS =
            CompositionBudget.TOTAL_READINGS_OF_ONE_CONDITION;

    private static final Allowances ONE_QUESTION = Allowances.DECLARED.with(QUESTIONS, 1);

    /** The readings of a condition held to a figure a chain of three choices runs into. */
    private static final Allowances FEW_READINGS = Allowances.DECLARED
            .with(CompositionBudget.READINGS_OF_ONE_CONDITION, 4)
            .with(READINGS, 8);

    private static final String NUMBERS = """
            module m

            let fits (limit: Int, n: Int): Bool = n >= limit

            behavior asked : (limit: Int, a: Int, b: Int) -> Bool
            let asked (limit, a, b) = List.any(n -> fits(limit, n), [ a, b ])
            """;

    private static final String CASES = """
            module m

            data Room = Kitchen | Study

            let fits (wanted: Room, room: Room): Bool = wanted == room

            behavior asked : (wanted: Room) -> Bool
            let asked (wanted) = List.any(room -> fits(wanted, room), [ Kitchen, Study ])
            """;

    /** A chain of choices, each {@code chosen} of the last and an input of its own. */
    private static String chain(String chosen) {
        return """
                module m

                let pick (a: Int, b: Int): Int = %s

                behavior asked : (n0: Int, h0: Int, h1: Int, h2: Int) -> Bool
                let asked (n0, h0, h1, h2) = {
                    let n1 = pick(n0, h0) + 1
                    let n2 = pick(n1, h1) + 1
                    let n3 = pick(n2, h2) + 1
                    n3 == 0
                }
                """.formatted(chosen);
    }

    private static Compilation compiled(String model, Allowances allowances) {
        return ACompiledModel.compiles(
                Compilation.ofSource(model, "Main").allowing(allowances));
    }

    private static Compilation leaving(String model, Allowances allowances) {
        Compilation compilation = Compilation.ofSource(model, "Main").allowing(allowances);
        compilation.leaveWhatIsToBeChanged();
        return ACompiledModel.compiles(compilation);
    }

    private static Optional<String> figure(Compilation compilation) {
        return Adequacy.leftToBeChanged(compilation.db(), "m", "asked").figure()
                .map(Figure::name);
    }

    @Test
    void aHelperComparingNumbersIsLeftAndOneComparingTheCasesOfASumIsMeasured() {
        assertEquals(Optional.of(QUESTIONS.name()), figure(leaving(NUMBERS, ONE_QUESTION)));

        Compilation cases = leaving(CASES, ONE_QUESTION);
        assertFalse(cases.db().ask(new HelpersReadOnApplicationsAroundThem("m", "asked")).value()
                .isEmpty(), "the same change is told of the helper over cases");
        assertEquals(Optional.empty(), figure(cases));
    }

    @Test
    void aChainOfChoicesIsLeftAndTheSameChainOfChoicesThatComeOutOneWayIsMeasured() {
        assertEquals(Optional.of(READINGS.name()),
                figure(leaving(chain("if a < b then a else b"), FEW_READINGS)));

        Compilation oneWay = leaving(chain("if 1 < 2 then a else b"), FEW_READINGS);
        assertTrue(oneWay.db().ask(new ConditionsReadThroughTooManyChoices("m", "asked")).value()
                .conditions() > 0, "the same change is told of the chain that comes out one way");
        assertEquals(Optional.empty(), figure(oneWay));
    }

    /** Dear and told of nothing: waiting is the only way to what its rows do not cover. */
    @Test
    void aBehaviorNoChangeIsToldOfIsMeasuredHoweverDear() {
        Compilation compilation = leaving("""
                module m
                behavior asked : (a: Int) -> Bool
                let asked (a) = a >= 1
                """, Allowances.DECLARED.with(QUESTIONS, 0));

        assertTrue(compilation.db().ask(new Adequacy.WhatStopsMeasuring("m", "asked")).value()
                .isPresent(), "measuring it runs into the figure");
        assertEquals(Optional.empty(), figure(compilation));
    }

    @Test
    void aBehaviorThatRunsIntoNoFigureIsMeasuredAndSoIsEveryOneWhereTheBuildDoesNotAsk() {
        assertEquals(Optional.empty(), figure(leaving(NUMBERS, Allowances.DECLARED)));
        assertEquals(Optional.empty(), figure(compiled(NUMBERS, ONE_QUESTION)));
    }

    /** What is told is what takes it out of the figure's way. */
    @Test
    void changedAsToldNothingIsLeft() {
        assertEquals(Optional.empty(), figure(leaving(
                NUMBERS.replace("let fits (limit: Int, n: Int): Bool = n >= limit", """
                        behavior fits : (limit: Int, n: Int) -> Bool
                        let fits (limit, n) = n >= limit"""), ONE_QUESTION)));
    }

    /** The body is read by no measure of the module, and that of the behavior beside it is. */
    @Test
    void theBodyIsReadByNoMeasureAndTheBodyBesideItIs() {
        Db db = leaving(NUMBERS + """

                behavior beside : (flag: Bool) -> Int
                let beside (flag) = if flag then 1 else 0
                """, ONE_QUESTION).db();
        Bodies.Elaborated checked = db.ask(new Bodies.Observable("m")).value();

        assertInstanceOf(BodyReading.ToBeChangedFirst.class,
                Adequacy.bodyReading(db, "m", checked, "asked"));
        assertInstanceOf(BodyReading.Read.class,
                Adequacy.bodyReading(db, "m", checked, "beside"));
        List<String> beside = List.of("beside");
        assertEquals(beside, List.copyOf(
                db.ask(new Adequacy.DecisionReadings("m")).value().keySet()));
        assertEquals(beside, List.copyOf(db.ask(new Adequacy.PathReached("m")).value().keySet()));
        assertEquals(beside, List.copyOf(db.ask(new Adequacy.Meets("m")).value().keySet()));
    }

    /** Nothing was shown of its rows, so the verdict is open and no gap is told; what is told is
     *  the figure and the change. */
    @Test
    void theReportSaysWhatToChangeInTheDocumentAndInBothLanguages() {
        Compilation compilation = Compilation.ofSource(NUMBERS, "Main").allowing(ONE_QUESTION);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.leaveWhatIsToBeChanged();
        AdequacyReport report = AdequacyReport.of(ACompiledModel.compiles(compilation));
        SourceRendering rendering = SourceRendering.namedByIdentity(compilation.texts());

        assertEquals(List.of("m.asked"), report.leftToBeChanged());
        assertEquals(AdequacyReport.AdequacyStatus.UNDETERMINED, report.adequacy());
        JsonNode document = JsonMapper.builder().build().readTree(report.json(rendering));
        DocumentShape.assertShapedLikeTheSchema(document);
        JsonNode asked = document.get("modules").get(0).get("behaviors").get(0);
        JsonNode helper = asked.get("toBeChangedFirst").get("helpersAppliedToEachElement").get(0);
        assertEquals("m.fits", helper.get("helper").asString());
        assertEquals(2, helper.get("applicationsAtMost").asInt());
        assertEquals("behavior_to_be_changed_first", asked.get("weakening").get(0).asString());

        String english = report.human(rendering, Locale.ENGLISH);
        assertTrue(english.contains("not measured: as it is written, measuring it stops at"),
                english);
        assertTrue(english.contains("Declared as a behavior, `fits` reads them once"), english);
        String japanese = report.human(rendering, Locale.JAPANESE);
        assertTrue(japanese.contains("測っていない: 今の書き方のまま測ると、途中で上限に達する"), japanese);
        assertTrue(japanese.contains("`fits` を behavior として宣言すると"), japanese);
    }
}
